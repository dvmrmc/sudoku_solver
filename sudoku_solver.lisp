;;; sudoku.clp
;;;============================================================================

;;; Fichero base para realizar el trabajo "Resolución deductiva del SUDOKU en
;;; CLIPS"

;;; Referencia Web: http://www.sudoku.org.uk/SudokuSolver/Solvers.asp
;;;                 http://www.sudoku.org.uk/SolvingSudoku.asp

;;;============================================================================

;;; Plantilla para representar las celdas del sudoku. Cada celda tiene los
;;; siguientes campos:
;;; - fila: Número de fila en la que se encuentra la celda
;;; - columna: Número de columna en la que se encuentra la celda
;;; - caja: Número de caja en el que se encuentra la celda
;;; - valor: Valor numérico de 1 a 9 asignado a la celda. Un valor 0 indica
;;;   que todavía no se conoce el valor numérido de la celda.
;;; - rango: Rango de valores que se pueden colocar en la celda. Inicialmente
;;;   el rango son todos los valores numéricos de 1 a 9.

(deftemplate celda
  (slot fila)
  (slot columna)
  (slot id)
  (slot caja)
  (slot valor
    (default 0))
  (multislot rango
         (default (create$ 1 2 3 4 5 6 7 8 9))))
    
;;;============================================================================

;;; La función "caja" calcula el caja en el que se encuentra una celda a
;;; partir de la fila y la columna:

(deffunction caja (?i ?j)
  (if (<= 1 ?i 3)
      then (if (<= 1 ?j 3)
           then 1
         else (if (<= 4 ?j 6)
              then 2
            else 3))
    else (if (<= 4 ?i 6)
         then (if (<= 1 ?j 3)
              then 4
            else (if (<= 4 ?j 6)
                 then 5
               else 6))
       else (if (<= 1 ?j 3)
            then 7
          else (if (<= 4 ?j 6)
               then 8
             else 9)))))
             
;;; Esta regla construye valores iniciales para todas las celdas de un sudoku
;;; en blanco

(defrule inicializa-valores
  (declare (salience 50))
  =>
  (assert (lee-ejemplo))
  (loop-for-count 
   (?i 1 9) 
   (loop-for-count 
    (?j 1 9) 
    (assert (celda (fila ?i)
           (columna ?j)
           (caja (caja ?i ?j))
           (id (+ (* 9 (- ?i 1)) ?j)))))))

;;;============================================================================

;;; Reglas para imprimir el resultado

(defrule imprime-sudoku
  (declare (salience 50))
  ?h <- (imprime)
  =>
  (printout t "+---+---+---+" t "|")
  (retract ?h)
  (assert (imprime 1 1)))

(defrule imprime-celda
  (declare (salience 50))
  ?h <- (imprime ?i ?j)
  (celda (fila ?i) (columna ?j) (valor ?v))
  =>
  (retract ?h)
  (if (= ?v 0) 
      then (printout t " ") 
    else (printout t ?v))
  (if (= (mod ?j 3) 0) 
      then (printout t "|"))
  (if (= (mod ?j 9) 0) 
      then (printout t t))
  (if (and (= (mod ?i 3) 0) (= (mod ?j 9) 0))
      then (printout t "+---+---+---+" t))
  (if (and (= (mod ?j 9) 0) (not (= ?i 9)))
      then (printout t "|")
    (assert (imprime (+ ?i 1) 1))
    else (assert (imprime ?i (+ ?j 1)))))

;;;============================================================================

;;; Función para leer un sudoku del fichero de ejemplos

(deffunction lee-sudoku (?n)
  (open "ejemplos.txt" data "r")
  (loop-for-count (?i 1 (- ?n 1))
          (loop-for-count (?j 1 11) (readline data)))
  (readline data)
  (loop-for-count 
   (?i 1 9)
   (bind ?fila (readline data))
    (loop-for-count
    (?j 1 9)
    (bind ?v (sub-string ?j ?j ?fila))
    (if (not (eq ?v "-"))
    then (assert (valor-inicial ?i ?j (nth 1 (explode$ ?v)))))))
  (close data))

;;; Reglas para la asignación de valores a partir de un ejemplo

(defrule sudoku-numero
  (declare (salience 50))
  ?h <- (lee-ejemplo)
  =>
  (retract ?h)
  (printout t "Que problema quieres resolver (1-100): ")
  (lee-sudoku (read)))

(defrule asigna-valor-inicial
  (declare (salience 50))
  ?h1 <- (celda (fila ?i) (columna ?j))
  ?h2 <- (valor-inicial ?i ?j ?v)
  =>
  (retract ?h2)
  (modify ?h1 (rango ?v) (valor ?v)))

(defrule presenta-sudoku-inicial
  (declare (salience 40))
  (not (valor-inicial ? ? ?))
  =>
  (assert (imprime)))

;;; =============================================================================================== 
;;; =============================================================================================== 
 
;;; Aquí empieza el código desarrollado por los alumnos:
;;;
;;; # David Martin Macías
;;; # Antonio J. González Rodríguez
;;;
;;; Explicaciones adicionales:

;;;   0.- Informe: Activación de la regla sobre informe de actividad de las estrategias

;;;   1.- Inicio: Reglas que inician el proceso iterativo

;;;   2.- Cambio-Fase: Reglas que mantienen el orden de ejecutción de las distintas fases

;;;   3.- Actualiza-Rangos: Reglas que actualizan los rangos al comienzo de cada iteración

;;;   4.- Actualiza-Valores: Reglas que actualizan los valores una vez se han ejecutado las estrategias

;;;   5.- Comprueba-fin: Reglas que comprueban si hay que repetir 

;;;   6.- Funciones auxliares: Funciones de agrupado para facilitar la construcción de estrategias complejas

;;; =============================================================================================== 
;;; =============================================================================================== 
 
 ;;Metemos en los hechos los estados de la ejecución genérica y las reglas de activación de estrategias
 (deffacts hechos
    (cambio-estado fin-actualiza-rangos ejecuta-estrategia)
    (cambio-estado fin-ejecuta-estrategia actualiza-valores)
    (cambio-estado fin-actualiza-valores comprueba-fin)
    (naked-pairs 1)
    (naked-triples 1)
    (hidden-singles 1)
    (hidden-pairs 1)
    (hidden-triples 1)
    (pointing-pairs 1)
    (box-reduction 1)
    (naked-quads 1)
    (hidden-quads 1)
    (x-wing 1)
    (swordfish 1)
    (jellyfish 1)
    (y-wing 1)
    (xyz-wing 1)
    (wxyz-wing 1)
    (unique-rectangles 1)
    (empty-rectangles 1))

(defglobal ?*max-iteraciones* = 5)
 
;;Fase de actualización de RANGOS
(defglobal ?*informar-actualizacion-rango* = FALSE)
(defglobal ?*informar-fin-actualizacion-rango* = FALSE) ;Separador de fase

;;Fase de actualización de VALORES
(defglobal ?*informar-actualizacion-valor* = FALSE) ;Informa cada vez que se toca el valor en una celda
(defglobal ?*informar-final* = TRUE) ;Informa del tiempo transcurrido
(defglobal ?*informar-fin-iteracion* = FALSE) ;Separador por iteraciones
(defglobal ?*informar-estrategias-basicas* = FALSE) ;Separador de Estrategias Basicas
(defglobal ?*informar-estrategias-avanzadas* = FALSE) ;Separador de Estrategias Avanzadas
(defglobal ?*informar-estrategias-unicidad* = FALSE) ;Separador de Estrategias de Unicidad

;;Fase de ejecución de ESTRATEGIAS
(defglobal ?*informar-naked-pairs* = FALSE) ;Informa cada vez que se aplica Naked pairs
(defglobal ?*informar-naked-triples* = FALSE) ;Informa cada vez que se aplica Naked triples
(defglobal ?*informar-hidden-singles* = FALSE) ;Informa cada vez que se aplica Hidden singles
(defglobal ?*informar-hidden-pairs* = FALSE) ;Informa cada vez que se aplica Hidden pairs
(defglobal ?*informar-hidden-triples* = FALSE) ;Informa cada vez que se aplica Hidden triples
(defglobal ?*informar-pointing-pairs* = FALSE) ;Informa cada vez que se aplica Pointing pairs
(defglobal ?*informar-box-reduction* = FALSE) ;Informa cada vez que se aplica Box reduction
(defglobal ?*informar-naked-quads* = FALSE) ;Informa cada vez que se aplica Naked Quads
(defglobal ?*informar-hidden-quads* = FALSE) ;Informa cada vez que se aplica Hidden quads
(defglobal ?*informar-x-wing* = FALSE) ;Informa cada vez que se aplica X-Wing
(defglobal ?*informar-swordfish* = FALSE) ;Informa cada vez que se aplica Swordfish
(defglobal ?*informar-jellyfish* = FALSE) ;Informa cada vez que se aplica Jellyfish
(defglobal ?*informar-y-wing* = FALSE) ;Informa cada vez que se aplica Y-Wing
(defglobal ?*informar-xyz-wing* = FALSE) ; Informa cada vez que se aplica XYZ-Wing 
(defglobal ?*informar-wxyz-wing* = FALSE) ; Informa cada vez que se aplica XYZ-Wing
(defglobal ?*informar-unique-rectangles* = FALSE) ;Informa cada vez que se aplica Unique-Rectangles
(defglobal ?*informar-empty-rectangles* = FALSE) ;Informa cada vez que se aplica Empty-Rectangles
 
;;; ==================================   INICIO  ==================================================

(defrule inicio
    ?h0 <- (imprime 9 10)
    (not (fin))
    =>
    (retract ?h0)
    (assert (tiempo1 (time)))
    (assert (iteraciones 1))
    (assert (estado actualiza-rangos)))

    
;;; ==================================   CAMBIO-ESTADO   ============================================

;;; FASE
;;;------------------------------------------------------------------------------------------------
(defrule cambio-fase
    ?h0 <- (estado ?anterior)
    (cambio-estado ?anterior ?siguiente)
    =>
    (retract ?h0)
    (if (eq ?siguiente ejecuta-estrategia) 
        then 
        (assert (estrategia-basica)))
    (assert (estado ?siguiente)))
    
;;; ESTRATEGIA-BASICA
;;;------------------------------------------------------------------------------------------------
(defrule comienzo-estrategia-basica
    (declare (salience 10))
    (estado ejecuta-estrategia)
    (estrategia-basica)
    =>
    (if ?*informar-estrategias-basicas* then (printout t "-- Estrategias Basicas --" crlf)))
    
(defrule fin-estrategia-basica
    (declare (salience -10))
    (estado ejecuta-estrategia)
    ?h0 <- (estrategia-basica)
    =>
    (retract ?h0)
    (assert (estrategia-avanzada)))
    
;;; ESTRATEGIA-AVANZADA
;;;------------------------------------------------------------------------------------------------
(defrule comienzo-estrategia-avanzada
    (declare (salience 10))
    (estado ejecuta-estrategia)
    (estrategia-avanzada)
    =>
    (if ?*informar-estrategias-avanzadas* then (printout t "-- Estrategias Avanzadas --" crlf)))
    
(defrule fin-estrategia-avanzada
    (declare (salience -10))
    (estado ejecuta-estrategia)
    ?h0 <- (estrategia-avanzada)
    =>
    (retract ?h0)
    (assert (estrategia-unicidad)))
    
;;; ESTRATEGIA-UNICIDAD
;;;------------------------------------------------------------------------------------------------
(defrule comienzo-estrategia-unicidad
    (declare (salience 10))
    (estado ejecuta-estrategia)
    (estrategia-unicidad)
    =>
    (if ?*informar-estrategias-unicidad* then (printout t "-- Estrategias Unicidad --" crlf)))
    
(defrule fin-estrategia-unicidad
    (declare (salience -10))
    (estado ejecuta-estrategia)
    ?h0 <- (estrategia-unicidad)
    =>
    (retract ?h0)
    (assert (estado fin-ejecuta-estrategia)))

;;; ==============================   ACTUALIZA-RANGOS    ==========================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule actualiza-rangos-fila
    (estado actualiza-rangos)
    ?h1 <- (celda (fila ?i) (valor ?valor&~0))
    ?h2 <- (celda (fila ?i) (valor 0) (rango $?a ?valor $?b) (columna ?x))
    (test (not (eq ?h1 ?h2)))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-actualizacion-rango* then (printout t "Actualizando rango de celda (" ?i "," ?x ")" crlf))
    (modify ?h2 (rango ?a ?b)))
             
;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
(defrule actualiza-rangos-columna
    (estado actualiza-rangos)
    ?h1 <- (celda (columna ?i) (valor ?valor&~0))
    ?h2 <- (celda (columna ?i) (valor 0) (rango $?a ?valor $?b) (fila ?x))
    (test (not (eq ?h1 ?h2)))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-actualizacion-rango* then (printout t "Actualizando rango de celda (" ?x "," ?i  ")" crlf))
    (modify ?h2 (rango ?a ?b)))

;;; CAJA
;;;------------------------------------------------------------------------------------------------
(defrule actualiza-rangos-caja
    (estado actualiza-rangos)
    ?h1 <- (celda (caja ?i) (valor ?valor&~0))
    ?h2 <- (celda (caja ?i) (valor 0) (rango $?a ?valor $?b) (fila ?x) (columna ?y))
    (test (not (eq ?h1 ?h2)))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-actualizacion-rango* then (printout t "Actualizando rango de celda (" ?x "," ?y ")" crlf))
    (modify ?h2 (rango ?a ?b)))

;;; FIN
;;;------------------------------------------------------------------------------------------------
(defrule fin-actualiza-rangos
    (declare (salience -10))
    ?h0 <- (estado actualiza-rangos)
    =>
    (retract ?h0)
    (assert (estado fin-actualiza-rangos))
    (if ?*informar-fin-actualizacion-rango* then (printout t "-- Fin fase rangos --" crlf)))


;;; ==================================   ACTUALIZA-VALORES   ======================================

(defrule actualiza-valores
    (estado actualiza-valores)
    ?h1 <- (celda (valor 0) (rango $?rango&:(eq (length ?rango) 1)) (fila ?i) (columna ?j))
    =>
    (if ?*informar-actualizacion-valor* then (printout t "Actualiza valor de celda (" ?i "," ?j ") a:" (nth 1 ?rango) crlf))
    (modify ?h1 (valor (nth 1 ?rango))))

(defrule fin-actualiza-valores
    ?h0 <- (estado actualiza-valores)
    (not (celda (valor 0) (rango $?rango&:(eq (length ?rango) 1))))
    =>
    (retract ?h0)
    (if ?*informar-actualizacion-valor* then (printout t "-- Fin fase valores --" crlf))
    (assert (estado fin-actualiza-valores)))

    
;;; ==================================   COMPRUEBA-FIN   ==========================================

(defrule fin-iteracion
    ?h0 <- (estado comprueba-fin)
    ?h1 <- (iteraciones ?i)
    (celda (valor 0))
    =>
    (retract ?h0 ?h1)
    (assert (iteraciones (+ ?i 1)))
    (if (> (+ ?i 1) ?*max-iteraciones*) 
        then
            (assert (fin-max-iteraciones))
        else
            (assert (estado actualiza-rangos))
            (if ?*informar-fin-iteracion* then (printout t "-- Fin de iteracion --" crlf))))

            
(defrule fin-max-iteraciones
    (fin-max-iteraciones)
    =>
    (if ?*informar-final* 
        then 
            (printout t "-- Maximo numero de iteraciones alcanzado --" crlf)
            (printout t crlf))
    (assert (fin-programa)))

    
(defrule fin-proceso
    ?h0 <- (estado comprueba-fin)
    (not (celda (valor 0)))
    =>
    (retract ?h0)
    (assert (celdas-completas))
    (assert (fin-programa)))

    
(defrule fin-programa-ok
    (declare (salience -10))
    (fin-programa)
    (not (fin))
    (tiempo1 ?t)
    (filas-ok)
    (columnas-ok)
    (cajas-ok)
    (celdas-completas)
    =>
    (assert (fin))
    (assert (imprime))
    (if ?*informar-final* 
        then 
            (printout t "---------- OK ----------" crlf)
            (printout t "Tiempo: "  (- (time) ?t) crlf)
            (printout t "------  Solucion  ------"  crlf)
            (printout t crlf)))

(defrule fin-programa-mal
    (declare (salience -10))
    (fin-programa)
    (not (fin))
    (tiempo1 ?t)
    (or
        (not (filas-ok))
        (not (columnas-ok))
        (not (cajas-ok))
        (not (celdas-completas)))
    =>
    (assert (fin))
    (assert (imprime))
    (if ?*informar-final* 
        then 
            (printout t "---------- MAL ----------" crlf)
            (printout t "Tiempo: "  (- (time) ?t) crlf)
            (printout t "------  Solucion  ------"  crlf)
            (printout t crlf)))

(defrule filas-ok
    (fin-programa)
    (not (and
        (celda (fila ?i) (id ?x) (valor ?valor&~0))
        (celda (fila ?i) (id ?y&~?x) (valor ?valor&~0))))
    =>
    (assert (filas-ok)))
    
(defrule columnas-ok    
    (fin-programa)
    (not (and
        (celda (columna ?i) (id ?x) (valor ?valor&~0))
        (celda (columna ?i) (id ?y&~?x) (valor ?valor&~0))))
    =>
    (assert (columnas-ok)))
    
(defrule cajas-ok
    (fin-programa)
    (not (and
            (celda (caja ?i) (id ?x) (valor ?valor&~0))
            (celda (caja ?i) (id ?y&~?x) (valor ?valor&~0))))
    =>
    (assert (cajas-ok)))

;;; ================================ FUNCIONES AUXILIARES =========================================

;;; FUNCIONES UNION  
;;;------------------------------------------------------------------------------------------------

;;;Union de dos listas (tipo multifield)
(deffunction union2-aux (?lista1 ?lista2)
    (if (or (eq (length ?lista1) 0) (eq (length ?lista2) 0))
        then ?lista2
        else 
            (if (member$ (first$ ?lista1) ?lista2)
                then (union2-aux (rest$ ?lista1) ?lista2)
                else (create$ (first$ ?lista1) (union2-aux (rest$ ?lista1) ?lista2))))) 

(deffunction union2 (?lista1 ?lista2)
    (sort > (union2-aux ?lista1 ?lista2)))

;;;Union de tres listas (tipo multifield)
(deffunction union3-aux (?lista1 ?lista2 ?lista3)
    (union2-aux ?lista1 (union2-aux ?lista2 ?lista3)))

(deffunction union3 (?lista1 ?lista2 ?lista3)
    (sort > (union3-aux ?lista1 ?lista2 ?lista3)))
    
;;;Union de cuatro listas (tipo multifield)
(deffunction union4-aux (?lista1 ?lista2 ?lista3 ?lista4)
    (union2-aux (union2-aux ?lista1 ?lista2) (union2-aux ?lista3 ?lista4)))

(deffunction union4 (?lista1 ?lista2 ?lista3 ?lista4)
    (sort > (union4-aux ?lista1 ?lista2 ?lista3 ?lista4)))
    
;;; FUNCIONES INTERSECCION
;;;------------------------------------------------------------------------------------------------

;;;Interseccion de dos listas (tipo multifield)
(deffunction interseccion2 (?lista1 ?lista2)
    (if (or (eq (length ?lista1) 0) (eq (length ?lista2) 0))    ;;podria solo comprobar una lista pero creo q es mejor si le pongo esta doble comprobacion. 
        then (create$)
        else
            (if (member$ (first$ ?lista1) ?lista2)
                then (create$ (first$ ?lista1) (interseccion2 (rest$ ?lista1) ?lista2))
                else (interseccion2 (rest$ ?lista1) ?lista2))))  
  
;;;Interseccion de tres listas (tipo multifield)
(deffunction interseccion3 (?lista1 ?lista2 ?lista3)
    (interseccion2 ?lista1 (interseccion2 ?lista2 ?lista3)))

;;;Interseccion de cuatro listas (tipo multifield)
(deffunction interseccion4 (?lista1 ?lista2 ?lista3 ?lista4)
    (interseccion2 (interseccion2 ?lista1 ?lista2) (interseccion2 ?lista3 ?lista4)))
    
;;; FUNCION DE VISIBILIDAD
;;;------------------------------------------------------------------------------------------------

(deffunction comparten-visibilidad (?fila1 ?columna1 ?caja1 ?fila2 ?columna2 ?caja2)
    (or 
        (eq ?fila1 ?fila2)
        (eq ?columna1 ?columna2)
        (eq ?caja1 ?caja2)))
    
;;; ===============================================================================================
;;; ===============================================================================================

;;;                                        ESTRATEGIAS

;;; Orden de las estrategias de las estrategias
;;;
;;;   BÁSICAS
;;;   1.- Naked Pairs: 
;;;   2.- Naked Triples:
;;;   3.- Hidden Singles:
;;;   4.- Hidden Pairs:
;;;   5.- Hidden Triples:
;;;   6.- Pointing Pairs:
;;;   7.- Box reduction:

;;;   AVANZADAS
;;;   8.- Naked Quads:
;;;   9.- Hiden Quads
;;;   10.- X-Wing:
;;;   11.- SwordFish:
;;;   12.- JellyFish:
;;;   13.- Y-Wing:
;;;   14.- XYZ-Wing
;;;   15.- WXYZ-Wing

;;;   UNICIDAD
;;;   16.- Unique Rectangles:
;;;   17.- Empty Rectangles:

;;; ===============================================================================================
;;; ===============================================================================================

        
;;; ===================================== NAKED PAIRS =============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule naked-pairs-fila
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-pairs 1)
    (celda (fila ?i) (id ?id1) (rango ?e1 ?e2))
    (celda (fila ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
    ?h0 <- (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango $?a ?e3&?e1|?e2 $?b) (columna ?x))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-pairs* then (printout t "Naked pairs FILA " ?i " (" ?e1 " " ?e2 ") en celda (" ?i "," ?x ")" crlf))
    (modify ?h0 (rango ?a ?b)))

;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
(defrule naked-pairs-columna
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-pairs 1)
    (celda (columna ?i) (id ?id1) (rango ?e1 ?e2))
    (celda (columna ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
    ?h0 <- (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango $?a ?e3&?e1|?e2 $?b) (fila ?x))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-pairs* then (printout t "Naked pairs COLUMNA " ?i " (" ?e1 " " ?e2 ") en celda (" ?x "," ?i ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    
;;; CAJA
;;;------------------------------------------------------------------------------------------------
(defrule naked-pairs-caja
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-pairs 1)
    (celda (caja ?i) (id ?id1)  (rango ?e1 ?e2))
    (celda (caja ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
    ?h0 <- (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango $?a ?e3&?e1|?e2 $?b) (fila ?x) (columna ?y))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-pairs* then (printout t "Naked pairs CAJA " ?i " (" ?e1 " " ?e2 ") en celda (" ?x "," ?y ")" crlf))
    (modify ?h0 (rango ?a ?b)))

;;; ====================================== NAKED-TRIPLES ==========================================

;;;------------------------------------------------------------------------------------------------
;;; FILA
;;;------------------------------------------------------------------------------------------------

;;; TRES DE 3
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-fila-tres-valores
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (fila ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (celda (fila ?i) (id ?id2&~?id1) (rango ?e1 ?e2 ?e3))
    (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango ?e1 ?e2 ?e3))
    ?h0 <- (celda (fila ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (columna ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples FILA(3d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?i "," ?j ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    
;;; DOS DE 3, UNA DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-fila-2de3-1de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (fila ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (celda (fila ?i) (id ?id2&~?id1) (rango ?e1 ?e2 ?e3))
    (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango ?e4&?e1|?e2 ?e5&?e2|?e3))
    ?h0 <- (celda (fila ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e6&?e1|?e2|?e3 $?b) (columna ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples FILA(2d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?i "," ?j ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    

;;; UNA DE 3, DOS DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-fila-1de3-2de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (fila ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (or
        (and 
            (celda (fila ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
            (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3)))
        (and 
            (celda (fila ?i) (id ?id2&~?id1) (rango ?e1 ?e3))
            (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3)))
        (and 
            (celda (fila ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
            (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango ?e1 ?e3))))
    ?h0 <- (celda (fila ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (columna ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples FILA(1d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?i "," ?j ")" crlf))
    (modify ?h0 (rango ?a ?b)))

    
;;; TRES DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-fila-3de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (fila ?i) (id ?id1) (rango ?e1 ?e2))
    (celda (fila ?i) (id ?id2&~?id1) (rango ?e1 ?e3))
    (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3))
    ?h0 <- (celda (fila ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (columna ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples FILA(0d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?i "," ?j ")" crlf))
    (modify ?h0 (rango ?a ?b)))

;;;------------------------------------------------------------------------------------------------
;;; COLUMNA
;;;------------------------------------------------------------------------------------------------

;;; TRES DE 3
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-columna-tres-valores
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (columna ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (celda (columna ?i) (id ?id2&~?id1) (rango ?e1 ?e2 ?e3))
    (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango ?e1 ?e2 ?e3))
    ?h0 <- (celda (columna ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (fila ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples COLUMNA(3d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?j "," ?i ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    
;;; DOS DE 3, UNA DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-columna-2de3-1de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (columna ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (celda (columna ?i) (id ?id2&~?id1) (rango ?e1 ?e2 ?e3))
    (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango ?e4&?e1|?e2 ?e5&?e2|?e3))
    ?h0 <- (celda (columna ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e6&?e1|?e2|?e3 $?b) (fila ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples COLUMNA(2d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?j "," ?i ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    

;;; UNA DE 3, DOS DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-columna-1de3-2de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (columna ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (or
        (and 
            ?h1 <- (celda (columna ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
            ?h2 <- (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3)))
        (and 
            ?h1 <- (celda (columna ?i) (id ?id2&~?id1) (rango ?e1 ?e3))
            ?h2 <- (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3)))
        (and 
            ?h1 <- (celda (columna ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
            ?h2 <- (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango ?e1 ?e3))))
    ?h0 <- (celda (columna ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (fila ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples COLUMNA(1d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?j "," ?i ")" crlf))
    (modify ?h0 (rango ?a ?b)))

    
;;; TRES DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-columna-3de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (columna ?i) (id ?id1) (rango ?e1 ?e2))
    (celda (columna ?i) (id ?id2&~?id1) (rango ?e1 ?e3))
    (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3))
    ?h0 <- (celda (columna ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (fila ?j))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples COLUMNA(0d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?j "," ?i ")" crlf))
    (modify ?h0 (rango ?a ?b)))

;;;------------------------------------------------------------------------------------------------
;;; CAJA
;;;------------------------------------------------------------------------------------------------

;;; TRES DE 3
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-caja-tres-valores
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (caja ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (celda (caja ?i) (id ?id2&~?id1) (rango ?e1 ?e2 ?e3))
    (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango ?e1 ?e2 ?e3))
    ?h0 <- (celda (caja ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (fila ?x) (columna ?y))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples CAJA(3d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?x "," ?y ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    
;;; DOS DE 3, UNA DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-caja-2de3-1de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (caja ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (celda (caja ?i) (id ?id2&~?id1) (rango ?e1 ?e2 ?e3))
    (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango ?e4&?e1|?e2 ?e5&?e2|?e3))
    ?h0 <- (celda (caja ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e6&?e1|?e2|?e3 $?b) (fila ?x) (columna ?y))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples CAJA(2d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?x "," ?y ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    

;;; UNA DE 3, DOS DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-caja-1de3-2de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (caja ?i) (id ?id1) (rango ?e1 ?e2 ?e3))
    (or
        (and 
            (celda (caja ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
            (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3)))
        (and 
            (celda (caja ?i) (id ?id2&~?id1) (rango ?e1 ?e3))
            (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3)))
        (and 
            (celda (caja ?i) (id ?id2&~?id1) (rango ?e1 ?e2))
            (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango ?e1 ?e3))))
    ?h0 <- (celda (caja ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (fila ?x) (columna ?y))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples CAJA(1d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?x "," ?y ")" crlf))
    (modify ?h0 (rango ?a ?b)))

    
;;; TRES DE 2
;;;------------------------------------------------------------------------------------------------
(defrule naked-triple-caja-3de2
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (naked-triples 1)
    (celda (caja ?i) (id ?id1) (rango ?e1 ?e2))
    (celda (caja ?i) (id ?id2&~?id1) (rango ?e1 ?e3))
    (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3))
    ?h0 <- (celda (caja ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e4&?e1|?e2|?e3 $?b) (fila ?x) (columna ?y))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-naked-triples* then (printout t "Naked triples CAJA(0d3) " ?i " - (" ?e1 " " ?e2 " " ?e3 ") en celda (" ?x "," ?y ")" crlf))
    (modify ?h0 (rango ?a ?b))) 
    
    
;;; ===================================== HIDDEN SINGLES ============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-singles-fila
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-singles 1)
    ?h0 <- (celda (fila ?i) (rango $?a ?e1 $?b) (id ?x) (columna ?j))
    (test (> (length (create$ ?a ?b)) 0))
    (not (celda (fila ?i) (rango $? ?e1 $?) (id ?y&~?x)))
    =>
    (if ?*informar-hidden-singles* then (printout t "Hidden singles FILA " ?i " (" ?e1 ") en celda (" ?i "," ?j ")" crlf))
    (modify ?h0 (rango ?e1)))

;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-singles-columna
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-singles 1)
    ?h0 <- (celda (columna ?i) (rango $?a ?e1 $?b) (id ?x) (fila ?j))
    (test (> (length (create$ ?a ?b)) 0))
    (not (celda (columna ?i) (rango $? ?e1 $?) (id ?y&~?x)))
    =>
    (if ?*informar-hidden-singles* then (printout t "Hidden singles COLUMNA " ?i " (" ?e1 ") en celda (" ?j "," ?i ")" crlf))
    (modify ?h0 (rango ?e1)))
    
;;; CAJA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-singles-caja
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-singles 1)
    ?h0 <- (celda (caja ?i) (rango $?a ?e1 $?b) (id ?x) (fila ?j) (columna ?k))
    (test (> (length (create$ ?a ?b)) 0))
    (not (celda (caja ?i) (rango $? ?e1 $?) (id ?y&~?x)))
    =>
    (if ?*informar-hidden-singles* then (printout t "Hidden singles CAJA " ?i " (" ?e1 ") en celda (" ?j "," ?k ")" crlf))
    (modify ?h0 (rango ?e1)))
    
;;; ===================================== HIDDEN PAIRS ============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-pairs-fila
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-pairs 1)
    ?h0 <- (celda (fila ?i) (valor 0) (rango $?a1 ?e1 $?b1 ?e2 $?c1) (id ?x) (columna ?m))
    ?h1 <- (celda (fila ?i) (valor 0) (rango $?a2 ?e1 $?b2 ?e2 $?c2) (id ?y&~?x) (columna ?n))
    (not   (celda (fila ?i) (rango $?a3 ?e3&?e1|?e2 $?b3) (id ?z&~?x&~?y) ))
    (test (> (length (create$ ?a1 ?b1 ?c1 ?a2 ?b2 ?c2))  0))
    =>
    (if ?*informar-hidden-pairs* then (printout t "Hidden pairs FILA " ?i " (" ?e1 " " ?e2 ") en celdas (" ?i "," ?m ") y (" ?i "," ?n ")" crlf))
    (modify ?h0 (rango ?e1 ?e2))
    (modify ?h1 (rango ?e1 ?e2)))

;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-pairs-columna
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-pairs 1)
    ?h0 <- (celda (columna ?x) (valor 0) (rango $?a1 ?e1 $?b1 ?e2 $?c1) (id ?i) (fila ?y))
    ?h1 <- (celda (columna ?x) (valor 0) (rango $?a2 ?e1 $?b2 ?e2 $?c2) (id ?j&~?i) (fila ?z))
    (not   (celda (columna ?x) (rango $?a3 ?e3&?e1|?e2 $?b3) (id ?k&~?i&~?j)))
    (test (> (length (create$ ?a1 ?b1 ?c1 ?a2 ?b2 ?c2))  0))
    =>
    (if ?*informar-hidden-pairs* then (printout t "Hidden pairs COLUMNA " ?x " (" ?e1 " " ?e2 ") en celdas (" ?y "," ?x ") y (" ?z "," ?x ")" crlf))
    (modify ?h0 (rango ?e1 ?e2))
    (modify ?h1 (rango ?e1 ?e2)))
    

;;; CAJA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-pairs-caja
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-pairs 1)
    ?h0 <- (celda (caja ?caja1) (valor 0) (rango $?a1 ?e1 $?b1 ?e2 $?c1) (id ?i) (fila ?w) (columna ?x))
    ?h1 <- (celda (caja ?caja1) (valor 0) (rango $?a2 ?e1 $?b2 ?e2 $?c2) (id ?j&~?i) (fila ?y) (columna ?z))
    (not   (celda (caja ?caja1) (rango $?a3 ?e3&?e1|?e2 $?b3) (id ?k&~?i&~?j)))
    (test (> (length (create$ ?a1 ?b1 ?c1 ?a2 ?b2 ?c2))  0))
    =>
    (if ?*informar-hidden-pairs* then (printout t "Hidden pairs CAJA (" ?e1 " " ?e2 ") en celdas (" ?w "," ?x ") y (" ?y "," ?z ")" crlf))
    (modify ?h0 (rango ?e1 ?e2))
    (modify ?h1 (rango ?e1 ?e2)))
    
;;; ===================================== HIDDEN TRIPLES ============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-triples-fila
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-triples 1)
    ?h0 <- (celda (fila ?i) (rango $?a1 ?e1 $?b1 ?e2 $?c1) (id ?x) (columna ?columna1))
    ?h1 <- (celda (fila ?i) (rango $?a2 ?e1 $?b2 ?e3 $?c2) (id ?y&~?x) (columna ?columna2))
    ?h2 <- (celda (fila ?i) (rango $?a3 ?e2 $?b3 ?e3 $?c3) (id ?z&~?x&~?y) (columna ?columna3))
    (test (and
            (or (and (member ?e3 ?c1)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))
            (or (and (member ?e2 ?b2)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))
            (or (and (member ?e1 ?a3)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))))
    (not   (celda (fila ?i) (rango $?a4 ?e4&?e1|?e2|?e3 $?b4) (id ?w&~?x&~?y&~?z) ))
    =>
    (if ?*informar-hidden-triples* then (printout t "Hidden triples FILA " ?i " (" ?e1 "," ?e2 "," ?e3  ") en celdas (" ?i "," ?columna1 "),(" ?i "," ?columna2 "),(" ?i "," ?columna3 ")" crlf))
    (if (member ?e3 ?c1) 
        then (modify ?h0 (rango ?e1 ?e2 ?e3))
        else (modify ?h0 (rango ?e1 ?e2)))
    (if (member ?e2 ?b2) 
        then (modify ?h1 (rango ?e1 ?e2 ?e3))
        else (modify ?h1 (rango ?e1 ?e3)))
    (if (member ?e1 ?a3) 
        then (modify ?h2 (rango ?e1 ?e2 ?e3))
        else (modify ?h2 (rango ?e2 ?e3))))

;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-triples-columna
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-triples 1)
    ?h0 <- (celda (columna ?i) (rango $?a1 ?e1 $?b1 ?e2 $?c1) (id ?x) (fila ?fila1))
    ?h1 <- (celda (columna ?i) (rango $?a2 ?e1 $?b2 ?e3 $?c2) (id ?y&~?x) (fila ?fila2))
    ?h2 <- (celda (columna ?i) (rango $?a3 ?e2 $?b3 ?e3 $?c3) (id ?z&~?x&~?y) (fila ?fila3))
    (test (and
            (or (and (member ?e3 ?c1)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))
            (or (and (member ?e2 ?b2)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))
            (or (and (member ?e1 ?a3)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))))
    (not   (celda (columna ?i) (rango $?a4 ?e4&?e1|?e2|?e3 $?b4) (id ?w&~?x&~?y&~?z) ))
    =>
    (if ?*informar-hidden-triples* then (printout t "Hidden triples COLUMNA " ?i " (" ?e1 "," ?e2 "," ?e3  ") en celdas (" ?fila1 "," ?i "),(" ?fila2 "," ?i "),(" ?fila3 "," ?i ")" crlf))
    (if (member ?e3 ?c1) 
        then (modify ?h0 (rango ?e1 ?e2 ?e3))
        else (modify ?h0 (rango ?e1 ?e2)))
    (if (member ?e2 ?b2) 
        then (modify ?h1 (rango ?e1 ?e2 ?e3))
        else (modify ?h1 (rango ?e1 ?e3)))
    (if (member ?e1 ?a3) 
        then (modify ?h2 (rango ?e1 ?e2 ?e3))
        else (modify ?h2 (rango ?e2 ?e3))))

;;; CAJA
;;;------------------------------------------------------------------------------------------------
(defrule hidden-triples-caja
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (hidden-triples 1)
    ?h0 <- (celda (caja ?i) (rango $?a1 ?e1 $?b1 ?e2 $?c1) (id ?x) (fila ?fila1) (columna ?columna1))
    ?h1 <- (celda (caja ?i) (rango $?a2 ?e1 $?b2 ?e3 $?c2) (id ?y&~?x) (fila ?fila2) (columna ?columna2))
    ?h2 <- (celda (caja ?i) (rango $?a3 ?e2 $?b3 ?e3 $?c3) (id ?z&~?x&~?y) (fila ?fila3) (columna ?columna3))
    (test (and
            (or (and (member ?e3 ?c1)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))
            (or (and (member ?e2 ?b2)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))
            (or (and (member ?e1 ?a3)       (> (length (create$ ?a1 ?b1 ?c1 ))  1))
                (and (not (member ?e3 ?c1)) (> (length (create$ ?a1 ?b1 ?c1 ))  0)))))
    (not   (celda (caja ?i) (rango $?a4 ?e4&?e1|?e2|?e3 $?b4) (id ?w&~?x&~?y&~?z) ))
    =>
    (if ?*informar-hidden-triples* then (printout t "Hidden triples CAJA " ?i " (" ?e1 "," ?e2 "," ?e3  ") en celdas (" ?fila1 "," ?columna1 "),(" ?fila2 "," ?columna2 "),(" ?fila3 "," ?columna3 ")" crlf))
    (if (member ?e3 ?c1) 
        then (modify ?h0 (rango ?e1 ?e2 ?e3))
        else (modify ?h0 (rango ?e1 ?e2)))
    (if (member ?e2 ?b2) 
        then (modify ?h1 (rango ?e1 ?e2 ?e3))
        else (modify ?h1 (rango ?e1 ?e3)))
    (if (member ?e1 ?a3) 
        then (modify ?h2 (rango ?e1 ?e2 ?e3))
        else (modify ?h2 (rango ?e2 ?e3))))
    
;;; ===================================== POINTING PAIRS ============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule pointing-pairs-fila
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (pointing-pairs 1)
    (celda (fila ?i) (caja ?c) (rango $? ?e1 $?))
    (not (celda (fila ?j&~?i) (caja ?c) (rango $? ?e1 $?)))
    ?h1 <- (celda (fila ?i) (caja ?d&~?c) (valor 0) (rango $?a ?e1 $?b) (columna ?x))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-pointing-pairs* then (printout t "Pointing pairs FILA " ?i " (" ?e1 ") en celda (" ?i "," ?x ")" crlf))
    (modify ?h1 (rango ?a ?b)))

    
;;; COLUMNA
;;;------------------------------------------------------------------------------------------------ 
(defrule pointing-pairs-columna
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (pointing-pairs 1)
    (celda (columna ?i) (caja ?c) (rango $? ?e1 $?))
    (not (celda (columna ?j&~?i) (caja ?c) (rango $? ?e1 $?)))
    ?h1 <- (celda (columna ?i) (caja ?d&~?c) (valor 0) (rango $?a ?e1 $?b) (fila ?x))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-pointing-pairs* then (printout t "Pointing pairs COLUMNA " ?i " (" ?e1 ") en celda (" ?x "," ?i ")" crlf))
    (modify ?h1 (rango ?a ?b)))
    
;;; ===================================== BOX REDUCTION ============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------ 

(defrule box-reduction-linea
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (box-reduction 1)
    (celda (fila ?i) (caja ?x) (rango $? ?e1 $?))
    (not (celda (fila ?i) (caja ?y&~?x) (rango $? ?e1 $?)))
    ?h0 <- (celda (fila ?j&~?i) (caja ?x) (valor 0) (rango $?a ?e1 $?b) (columna ?k))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-box-reduction* then (printout t "Box reduction FILA " ?i " con el número (" ?e1 ") en celda (" ?j "," ?k ")" crlf))
    (modify ?h0 (rango ?a ?b)))

;;; COLUMNA
;;;------------------------------------------------------------------------------------------------ 
    
(defrule box-reduction-columna
    (estado ejecuta-estrategia)
    (estrategia-basica)
    (box-reduction 1)
    (celda (columna ?i) (caja ?x) (rango $? ?e1 $?))
    (not (celda (columna ?i) (caja ?y&~?x) (rango $? ?e1 $?)))
    ?h0 <- (celda (columna ?j&~?i) (caja ?x) (valor 0) (rango $?a ?e1 $?b) (fila ?k))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-box-reduction* then (printout t "Box reduction COLUMNA " ?i " con el número (" ?e1 ") en celda (" ?k "," ?j ")" crlf))
    (modify ?h0 (rango ?a ?b)))
    
    
;;; ==============================================================================================  
;;; ===================================== AVANZADAS   ============================================  
;;; ==============================================================================================  
    
    
;;; ===================================== NAKED QUADS ============================================  

;;; FILA
;;;------------------------------------------------------------------------------------------------

(defrule naked-quads-fila
    (naked-quads 1)
    (estado ejecuta-estrategia)
    ?h0 <-(estrategia-avanzada)
    ?h1 <- (celda (fila ?i) (id ?id1) (rango $?rango1&:(<= 2 (length $?rango1) 4)))
    ?h2 <- (celda (fila ?i) (id ?id2&~?id1) (rango $?rango2&:(and (<= 2 (length $?rango2) 4) (<= (length (union2 $?rango1 $?rango2)) 4))))
    ?h3 <- (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango $?rango3&:(and (<= 2 (length $?rango3) 4) (<= (length (union3 $?rango1 $?rango2 $?rango3)) 4))))
    ?h4 <- (celda (fila ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?rango4&:(and (<= 2 (length $?rango4) 4) (= (length (union4 $?rango1 $?rango2 $?rango3 $?rango4)) 4))))
    ?h5 <- (celda (fila ?i) (columna ?j) (id ?id5&~?id1&~?id2&~?id3&~?id4)  (rango $?a ?e1&:(member$ ?e1 (union4 $?rango1 $?rango2 $?rango3 $?rango4)) $?b))
    =>
    (if ?*informar-naked-quads* then (printout t "Naked Quads Fila: Detectado en la fila " ?i " con los valores " (union4 $?rango1 $?rango2 $?rango3 $?rango4) ". Se ha eliminado el valor " ?e1 " de la celda " ?i "," ?j crlf))
    (modify ?h5 (rango $?a $?b))
    (retract ?h0)
    (assert (estrategia-basica)))
    

;;; COLUMNA
;;;------------------------------------------------------------------------------------------------

(defrule naked-quads-columna
    (naked-quads 1)
    (estado ejecuta-estrategia)
    ?h0 <-(estrategia-avanzada)
    ?h1 <- (celda (columna ?i) (id ?id1) (rango $?rango1&:(<= 2 (length $?rango1) 4)))
    ?h2 <- (celda (columna ?i) (id ?id2&~?id1) (rango $?rango2&:(and (<= 2 (length $?rango2) 4) (<= (length (union2 $?rango1 $?rango2)) 4))))
    ?h3 <- (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango $?rango3&:(and (<= 2 (length $?rango3) 4) (<= (length (union3 $?rango1 $?rango2 $?rango3)) 4))))
    ?h4 <- (celda (columna ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?rango4&:(and (<= 2 (length $?rango4) 4) (= (length (union4 $?rango1 $?rango2 $?rango3 $?rango4)) 4))))
    ?h5 <- (celda (columna ?i) (fila ?j) (id ?id5&~?id1&~?id2&~?id3&~?id4)  (rango $?a ?e1&:(member$ ?e1 (union4 $?rango1 $?rango2 $?rango3 $?rango4)) $?b))
    =>
    (if ?*informar-naked-quads* then (printout t "Naked Quads Columna: Detectado en la columna " ?i " con los valores " (union4 $?rango1 $?rango2 $?rango3 $?rango4) ". Se ha eliminado el valor " ?e1 " de la celda " ?j "," ?i crlf))
    (modify ?h5 (rango $?a $?b))
    (retract ?h0)
    (assert (estrategia-basica)))
    
;;;------------------------------------------------------------------------------------------------
;;; CAJA
;;;------------------------------------------------------------------------------------------------

(defrule naked-quads-caja
    (naked-quads 1)
    (estado ejecuta-estrategia)
    ?h0 <-(estrategia-avanzada)
    ?h1 <- (celda (caja ?i) (id ?id1) (rango $?rango1&:(<= 2 (length $?rango1) 4)))
    ?h2 <- (celda (caja ?i) (id ?id2&~?id1) (rango $?rango2&:(and (<= 2 (length $?rango2) 4) (<= (length (union2 $?rango1 $?rango2)) 4))))
    ?h3 <- (celda (caja ?i) (id ?id3&~?id1&~?id2) (rango $?rango3&:(and (<= 2 (length $?rango3) 4) (<= (length (union3 $?rango1 $?rango2 $?rango3)) 4))))
    ?h4 <- (celda (caja ?i) (id ?id4&~?id1&~?id2&~?id3) (rango $?rango4&:(and (<= 2 (length $?rango4) 4) (= (length (union4 $?rango1 $?rango2 $?rango3 $?rango4)) 4))))
    ?h5 <- (celda (caja ?i) (fila ?fila) (columna ?columna) (id ?id5&~?id1&~?id2&~?id3&~?id4)  (rango $?a ?e1&:(member$ ?e1 (union4 $?rango1 $?rango2 $?rango3 $?rango4)) $?b))
    =>
    (if ?*informar-naked-quads* then (printout t "Naked Quads Caja: Detectado en la caja " ?i " con los valores " (union4 $?rango1 $?rango2 $?rango3 $?rango4) ". Se ha eliminado el valor " ?e1 " de la celda " ?fila "," ?columna crlf))
    (modify ?h5 (rango $?a $?b))
    (retract ?h0)
    (assert (estrategia-basica)))       
    
;;; ===================================== HIDDEN QUADS ============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
    
(defrule hidden-quads-fila
  (estado ejecuta-estrategia)
  ?h0 <- (estrategia-avanzada)
  (hidden-quads 1)
  ?h1 <- (celda (fila ?i) (id ?id1) (rango $?rango1))
  ?h2 <- (celda (fila ?i) (id ?id2&~?id1)  (rango $?rango2))
  (test
        (<= 2 (length (interseccion2 $?rango1 $?rango2)) 4))        
  ?h3 <- (celda (fila ?i) (id ?id3&~?id2&~?id1)   (rango $?rango3))
  (test
    (and
        (<= 2 (length (interseccion2 $?rango1 $?rango3)) 4)
        (<= 2 (length (interseccion2 $?rango2 $?rango3)) 4)))   
  ?h4 <- (celda (fila ?i) (id ?id4&~?id3&~?id2&~?id1)  (rango $?rango4))
  (test
    (and
        (<= 2 (length (interseccion2 $?rango1 $?rango4)) 4)
        (<= 2 (length (interseccion2 $?rango2 $?rango4)) 4)
        (<= 2 (length (interseccion2 $?rango3 $?rango4)) 4)
        (eq (length (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4)))) 4)))
    ;;;la condicion asegura que la longitud de la union de las intersecciones de los rangos de las celdas candidatas sea 4, para ello lo comprobamos con interseccion 2 a 2.  
  (not (celda (fila ?i) (id ?id5&~?id4&~?id3&~?id2&~?id1) (rango $? ?e1&:(not (member$ ?e1 (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4))))) $?)))
   =>
  (bind $?salida (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4))))
  (if ?*informar-hidden-quads*  then (printout t "Hidden quads FILA: detectado en la fila " ?i " con los valores " $?salida crlf))
  (modify ?h1 (rango (interseccion2 $?rango1 $?salida)))
  (modify ?h2 (rango (interseccion2 $?rango2 $?salida)))
  (modify ?h3 (rango (interseccion2 $?rango3 $?salida)))
  (modify ?h4 (rango (interseccion2 $?rango4 $?salida)))
  (retract ?h0)
  (assert (estrategia-basica)))
  
  
;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
    
(defrule hidden-quads-columna
  (estado ejecuta-estrategia)
  ?h0 <- (estrategia-avanzada)
  (hidden-quads 1)
  ?h1 <- (celda (columna ?i) (id ?id1) (rango $?rango1))
  ?h2 <- (celda (columna ?i) (id ?id2&~?id1)  (rango $?rango2))
  (test
        (<= 2 (length (interseccion2 $?rango1 $?rango2)) 4))        
  ?h3 <- (celda (columna ?i) (id ?id3&~?id2&~?id1)   (rango $?rango3))
  (test
    (and
        (<= 2 (length (interseccion2 $?rango1 $?rango3)) 4)
        (<= 2 (length (interseccion2 $?rango2 $?rango3)) 4)))   
  ?h4 <- (celda (columna ?i) (id ?id4&~?id3&~?id2&~?id1)  (rango $?rango4))
  (test
    (and
        (<= 2 (length (interseccion2 $?rango1 $?rango4)) 4)
        (<= 2 (length (interseccion2 $?rango2 $?rango4)) 4)
        (<= 2 (length (interseccion2 $?rango3 $?rango4)) 4)
        (eq (length (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4)))) 4)))
    ;;;la condicion asegura que la longitud de la union de las intersecciones de los rangos de las celdas candidatas sea 4, para ello lo comprobamos con interseccion 2 a 2.  
  (not (celda (columna ?i) (id ?id5&~?id4&~?id3&~?id2&~?id1) (rango $? ?e1&:(not (member$ ?e1 (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4))))) $?)))
   =>
  (bind $?salida (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4))))
  (if ?*informar-hidden-quads*  then (printout t "Hidden quads COLUMNA: detectado en la columna " ?i " con los valores " $?salida crlf))
  (modify ?h1 (rango (interseccion2 $?rango1 $?salida)))
  (modify ?h2 (rango (interseccion2 $?rango2 $?salida)))
  (modify ?h3 (rango (interseccion2 $?rango3 $?salida)))
  (modify ?h4 (rango (interseccion2 $?rango4 $?salida)))
  (retract ?h0)
  (assert (estrategia-basica)))
  
 
;;; CAJA
;;;------------------------------------------------------------------------------------------------
    
(defrule hidden-quads-caja
  (estado ejecuta-estrategia)
  ?h0 <- (estrategia-avanzada)
  (hidden-quads 1)
  ?h1 <- (celda (caja ?i) (id ?id1) (rango $?rango1))
  ?h2 <- (celda (caja ?i) (id ?id2&~?id1)  (rango $?rango2))
  (test
        (<= 2 (length (interseccion2 $?rango1 $?rango2)) 4))        
  ?h3 <- (celda (caja ?i) (id ?id3&~?id2&~?id1)   (rango $?rango3))
  (test
    (and
        (<= 2 (length (interseccion2 $?rango1 $?rango3)) 4)
        (<= 2 (length (interseccion2 $?rango2 $?rango3)) 4)))   
  ?h4 <- (celda (caja ?i) (id ?id4&~?id3&~?id2&~?id1)  (rango $?rango4))
  (test
    (and
        (<= 2 (length (interseccion2 $?rango1 $?rango4)) 4)
        (<= 2 (length (interseccion2 $?rango2 $?rango4)) 4)
        (<= 2 (length (interseccion2 $?rango3 $?rango4)) 4)
        (eq (length (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4)))) 4)))
    ;;;la condicion asegura que la longitud de la union de las intersecciones de los rangos de las celdas candidatas sea 4, para ello lo comprobamos con interseccion 2 a 2.  
  (not (celda (caja ?i) (id ?id5&~?id4&~?id3&~?id2&~?id1) (rango $? ?e1&:(not (member$ ?e1 (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4))))) $?)))
   =>
  (bind $?salida (union2 (union4 (interseccion2 $?rango1 $?rango2) (interseccion2 $?rango1 $?rango3) (interseccion2 $?rango1 $?rango4) (interseccion2 $?rango2 $?rango3)) (union2 (interseccion2 $?rango2 $?rango4) (interseccion2 $?rango3 $?rango4))))
  (if ?*informar-hidden-quads*  then (printout t "Hidden quads CAJA: detectado en la caja " ?i " con los valores " $?salida crlf))
  (modify ?h1 (rango (interseccion2 $?rango1 $?salida)))
  (modify ?h2 (rango (interseccion2 $?rango2 $?salida)))
  (modify ?h3 (rango (interseccion2 $?rango3 $?salida)))
  (modify ?h4 (rango (interseccion2 $?rango4 $?salida)))
  (retract ?h0)
  (assert (estrategia-basica)))
    
;;; ===================================== X-WING ============================================

;;; FILA
;;;------------------------------------------------------------------------------------------------ 
(defrule x-wing-fila-caso1
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (x-wing 1)
    ;PAR 1
    (celda (fila ?i) (columna ?x) (id ?id1) (rango $? ?e1 $?))
    (celda (fila ?i) (columna ?y) (id ?id2&~?id1) (rango $? ?e1 $?))
    (not (celda (fila ?i) (id ?id3&~?id1&~?id2) (rango $? ?e1 $?)))
    ;PAR2
    (celda (fila ?j&~?i) (columna ?x) (id ?id3) (rango $? ?e1 $?))
    (celda (fila ?j) (columna ?y) (id ?id4&~?id3) (rango $? ?e1 $?))
    (not (celda (fila ?j) (id ?id5&~?id3&~?id4) (rango $? ?e1 $?)))
    ;Celda eliminable
    ?h0 <- (celda (fila ?k&~?i&~?j) (columna ?z&?x|?y) (rango $?a ?e1 $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-x-wing* then (printout t "X-Wing FILAS " ?i "," ?j " con el número (" ?e1 ") en celda (" ?k "," ?z ")" crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
(defrule x-wing-fila-caso2
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (x-wing 1)
    ;PAR1
    (celda (fila ?i) (columna ?x) (id ?id1) (caja ?c) (rango $? ?e1 $?))
    (celda (fila ?i) (columna ?y) (id ?id2&~?id1) (caja ?d&~?c) (rango $? ?e1 $?))
    (not (celda (fila ?i) (columna ?w&~?x&~?y) (id ?id3&~?id1&~?id2) (rango $? ?e1 $?)))
    ;PAR2
    (celda (fila ?j&~?i) (columna ?x) (id ?id3) (caja ?c) (rango $? ?e1 $?))
    (celda (fila ?j) (columna ?y) (id ?id4&~?id3) (caja ?d) (rango $? ?e1 $?))
    (not (celda (fila ?j) (columna ?z&~?x&~?y) (id ?id5&~?id3&~?id4) (rango $? ?e1 $?)))
    ;Celda eliminable
    ?h0 <- (celda (fila ?k&~?i&~?j) (columna ?columna) (caja ?e&?c|?d) (rango $?a ?e1 $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-x-wing* then (printout t "X-Wing FILAS " ?i "," ?j " con el número (" ?e1 ") en celda (" ?k "," ?columna ")" crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;; COLUMNA
;;;------------------------------------------------------------------------------------------------ 
(defrule x-wing-columna-caso1
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (x-wing 1)
    ;PAR 1
    (celda (columna ?i) (fila ?x) (id ?id1) (rango $? ?e1 $?))
    (celda (columna ?i) (fila ?y) (id ?id2&~?id1) (rango $? ?e1 $?))
    (not (celda (columna ?i) (id ?id3&~?id1&~?id2) (rango $? ?e1 $?)))
    ;PAR2
    (celda (columna ?j&~?i) (fila ?x) (id ?id3) (rango $? ?e1 $?))
    (celda (columna ?j) (fila ?y) (id ?id4&~?id3) (rango $? ?e1 $?))
    (not (celda (columna ?j) (id ?id5&~?id3&~?id4) (rango $? ?e1 $?)))
    ;Celda eliminable
    ?h0 <- (celda (columna ?k&~?i&~?j) (fila ?z&?x|?y) (rango $?a ?e1 $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-x-wing* then (printout t "X-Wing COLUMNAS " ?i "," ?j " con el número (" ?e1 ") en celda (" ?z "," ?k ")" crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
(defrule x-wing-columna-caso2
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (x-wing 1)
    ;PAR1
    (celda (columna ?i) (fila ?x) (id ?id1) (caja ?c) (rango $? ?e1 $?))
    (celda (columna ?i) (fila ?y) (id ?id2&~?id1) (caja ?d&~?c) (rango $? ?e1 $?))
    (not (celda (columna ?i) (fila ?w&~?x&~?y) (id ?id3&~?id1&~?id2) (rango $? ?e1 $?)))
    ;PAR2
    (celda (columna ?j&~?i) (fila ?x) (id ?id3) (caja ?c) (rango $? ?e1 $?))
    (celda (columna ?j) (fila ?y) (id ?id4&~?id3) (caja ?d) (rango $? ?e1 $?))
    (not (celda (columna ?j) (fila ?z&~?x&~?y) (id ?id5&~?id3&~?id4) (rango $? ?e1 $?)))
    ;Celda eliminable
    ?h0 <- (celda (columna ?k&~?i&~?j) (fila ?fila) (caja ?e&?c|?d) (rango $?a ?e1 $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-x-wing* then (printout t "X-Wing COLUMNAS " ?i "," ?j " con el número (" ?e1 ") en celda (" ?fila "," ?k ")" crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))

;;; CAJA
;;;------------------------------------------------------------------------------------------------ 
(defrule x-wing-caja-caso1
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (x-wing 1)
    ;PAR1
    (celda (fila ?i)     (caja ?c1) (id ?id1) (rango $? ?e1 $?))
    (celda (fila ?j&~?i) (caja ?c1) (id ?id2&~?id1) (rango $? ?e1 $?))
    (not (celda (caja ?c1) (rango $? ?e1 $?) (id ?id3&~?id1&~?id2)))
    ;PAR2
    (celda (fila ?i)     (caja ?c2&~?c1) (id ?id4)       (rango $? ?e1 $?))
    (celda (fila ?j&~?i) (caja ?c2)      (id ?id5&~?id4) (rango $? ?e1 $?))
    (not (celda (caja ?c2) (rango $? ?e1 $?) (id ?id6&~?id4&~?id5)))
    ?h0 <- (celda (fila ?k&?i|?j) (columna ?columna) (caja ?c3&~?c1&~?c2) (rango $?a ?e1 $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-x-wing* then (printout t "X-Wing CAJA " ?c1 "," ?c2 " con el número (" ?e1 ") en celda (" ?k "," ?columna ")" crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))

(defrule x-wing-caja-caso2
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (x-wing 1)
    ;PAR1
    (celda (columna ?i)     (caja ?c1) (id ?id1) (rango $? ?e1 $?))
    (celda (columna ?j&~?i) (caja ?c1) (id ?id2&~?id1) (rango $? ?e1 $?))
    (not (celda (caja ?c1) (rango $? ?e1 $?)  (id ?id3&~?id1&~?id2)))
    ;PAR2
    (celda (columna ?i)     (caja ?c2&~?c1) (id ?id4) (rango $? ?e1 $?))
    (celda (columna ?j&~?i) (caja ?c2)      (id ?id5&~?id4) (rango $? ?e1 $?))
    (not (celda (caja ?c2) (rango $? ?e1 $?) (id ?id6&~?id4&~?id5)))
    ?h0 <- (celda (columna ?k&?i|?j) (fila ?fila) (caja ?c3&~?c1&~?c2) (rango $?a ?e1 $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-x-wing* then (printout t "X-Wing CAJA " ?c1 "," ?c2 " con el número (" ?e1 ") en celda (" ?fila "," ?k ")" crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;; ===================================== SWORDFISH =================================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule swordfish-fila
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (swordfish 1)
    ;FILA 1
    (celda (fila ?i) (columna ?x) (rango $? ?e1 $?) (id ?id1))
    (celda (fila ?i) (columna ?y) (rango $? ?e1 $?) (id ?id2&~?id1))   
    (celda (fila ?i) (columna ?z) (id ?id3&~?id1&~?id2))
    (not (celda (fila ?i) (columna ?o&~?x&~?y&~?z) (rango $? ?e1 $?)))
    ;FILA 2
    (celda (fila ?j&~?i) (columna ?x) (rango $? ?e1 $?) (id ?id4))
    (celda (fila ?j)     (columna ?y) (id ?id5&~?id4))   
    (celda (fila ?j)     (columna ?z) (rango $? ?e1 $?) (id ?id6&~?id4&~?id5))
    (not (celda (fila ?j) (columna ?p&~?x&~?y&~?z) (rango $? ?e1 $?)))
    ;FILA 3
    (celda (fila ?k&~?i&~?j) (columna ?x) (id ?id7))
    (celda (fila ?k)         (columna ?y) (rango $? ?e1 $?) (id ?id8&~?id7))
    (celda (fila ?k)         (columna ?z) (rango $? ?e1 $?) (id ?id9&~?id7&~?id8))
    (not (celda (fila ?k) (columna ?q&~?x&~?y&~?z) (rango $? ?e1 $?)))
    ;Celda eliminable
    ?h0 <- (celda (fila ?fila&~?i&~?j&~?k) (columna ?columna&?x|?y|?z) (rango $?a ?e1 $?b))
    (test (< (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-swordfish* then (printout t "Swordfish filas(" ?i "," ?j "," ?k ") y columnas(" ?x "," ?y "," ?z ") para el candidato " ?e1 " sobre celda " ?fila "," ?columna crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
(defrule swordfish-columna
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (swordfish 1)
    ;FILA 1
    (celda (columna ?i) (fila ?x) (rango $? ?e1 $?) (id ?id1))
    (celda (columna ?i) (fila ?y) (rango $? ?e1 $?) (id ?id2&~?id1))   
    (celda (columna ?i) (fila ?z) (id ?id3&~?id1&~?id2))
    (not (celda (columna ?i) (fila ?o&~?x&~?y&~?z) (rango $? ?e1 $?)))
    ;FILA 2
    (celda (columna ?j&~?i) (fila ?x) (rango $? ?e1 $?) (id ?id4))
    (celda (columna ?j)     (fila ?y) (id ?id5&~?id4))   
    (celda (columna ?j)     (fila ?z) (rango $? ?e1 $?) (id ?id6&~?id4&~?id5))
    (not (celda (columna ?j) (fila ?p&~?x&~?y&~?z) (rango $? ?e1 $?)))
    ;FILA 3
    (celda (columna ?k&~?i&~?j) (fila ?x) (id ?id7))
    (celda (columna ?k)         (fila ?y) (rango $? ?e1 $?) (id ?id8&~?id7))
    (celda (columna ?k)         (fila ?z) (rango $? ?e1 $?) (id ?id9&~?id7&~?id8))
    (not (celda (columna ?k) (fila ?q&~?x&~?y&~?z) (rango $? ?e1 $?)))
    ;Celda eliminable
    ?h0 <- (celda (columna ?columna&~?i&~?j&~?k) (fila ?fila&?x|?y|?z) (rango $?a ?e1 $?b))
    (test (< (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-swordfish* then (printout t "Swordfish columnas(" ?i "," ?j "," ?k ") y columnas(" ?x "," ?y "," ?z ") para el candidato " ?e1 " sobre celda " ?fila "," ?columna crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;; ===================================== JELLYFISH =================================================

;;; FILA
;;;------------------------------------------------------------------------------------------------
(defrule jellyfish-fila
    (estado ejecuta-estrategia)
    ?h0 <- (estrategia-avanzada)
    (jellyfish 1)
    ;FILA1
    (celda (fila ?i) (columna ?w) (rango $? ?e $?) (id ?id1))
    (celda (fila ?i) (columna ?x) (rango $? ?e $?) (id ?id2&~?id1))   
    (celda (fila ?i) (columna ?y) (id ?id3&~?id1&~?id2))
    (celda (fila ?i) (columna ?z) (id ?id4&~?id1&~?id2&~?id3))
    (not (celda (fila ?i) (columna ?columna1&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;FILA2
    (celda (fila ?j&~?i) (columna ?w) (rango $?r1))
    (celda (fila ?j)     (columna ?x) (rango $?r2))
    (celda (fila ?j)     (columna ?y) (rango $?r3))
    (celda (fila ?j)     (columna ?z) (rango $?r4))
    (test (or 
            (and (member$ ?e $?r1) (member$ ?e $?r2)) 
            (and (member$ ?e $?r1) (member$ ?e $?r3)) 
            (and (member$ ?e $?r1) (member$ ?e $?r4)) 
            (and (member$ ?e $?r2) (member$ ?e $?r3)) 
            (and (member$ ?e $?r2) (member$ ?e $?r4)) 
            (and (member$ ?e $?r3) (member$ ?e $?r4))))
    (not (celda (fila ?j) (columna ?columna2&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;FILA3
    (celda (fila ?k&~?i&~?j) (columna ?w) (rango $?r5))
    (celda (fila ?k)         (columna ?x) (rango $?r6))
    (celda (fila ?k)         (columna ?y) (rango $?r7))
    (celda (fila ?k)         (columna ?z) (rango $?r8))
    (test (or 
            (and (member$ ?e $?r5) (member$ ?e $?r6)) 
            (and (member$ ?e $?r5) (member$ ?e $?r7)) 
            (and (member$ ?e $?r5) (member$ ?e $?r8)) 
            (and (member$ ?e $?r6) (member$ ?e $?r7)) 
            (and (member$ ?e $?r6) (member$ ?e $?r8)) 
            (and (member$ ?e $?r7) (member$ ?e $?r8))))
    (not (celda (fila ?k) (columna ?columna3&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;FILA4
    (celda (fila ?l&~?i&~?j&~?k) (columna ?w) (rango $?r9))
    (celda (fila ?l)             (columna ?x) (rango $?r10))
    (celda (fila ?l)             (columna ?y) (rango $?r11))
    (celda (fila ?l)             (columna ?z) (rango $?r12))
    (test (or 
            (and (member$ ?e $?r9) (member$ ?e $?r10)) 
            (and (member$ ?e $?r9) (member$ ?e $?r11)) 
            (and (member$ ?e $?r9) (member$ ?e $?r12)) 
            (and (member$ ?e $?r10) (member$ ?e $?r11)) 
            (and (member$ ?e $?r10) (member$ ?e $?r12)) 
            (and (member$ ?e $?r11) (member$ ?e $?r12))))
    (not (celda (fila ?l) (columna ?columna4&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;;Celda con candidato eliminable
    ?h1 <- (celda (fila ?fila&~?i&~?j&~?k&~?l) (columna ?columna&?w|?x|?y|?z) (rango $?a ?e $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-jellyfish* then (printout t "JellyFish FILA para filas(" ?i "," ?j "," ?k "," ?l ") y columnas(" ?w "," ?x "," ?y "," ?z ") para el candidato " ?e " sobre celda " ?fila "," ?columna crlf))
    (modify ?h1 (rango ?a ?b))
    (retract ?h0)
    (assert (estrategia-basica)))
  
;;; COLUMNA
;;;------------------------------------------------------------------------------------------------
(defrule jellyfish-columna
    (estado ejecuta-estrategia)
    ?h0 <- (estrategia-avanzada)
    (jellyfish 1)
    ;FILA1
    (celda (columna ?i) (fila ?w) (rango $? ?e $?) (id ?id1))
    (celda (columna ?i) (fila ?x) (rango $? ?e $?) (id ?id2&~?id1))   
    (celda (columna ?i) (fila ?y) (id ?id3&~?id1&~?id2))
    (celda (columna ?i) (fila ?z) (id ?id4&~?id1&~?id2&~?id3))
    (not (celda (columna ?i) (fila ?fila1&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;FILA2
    (celda (columna ?j&~?i) (fila ?w) (rango $?r1))
    (celda (columna ?j)     (fila ?x) (rango $?r2))
    (celda (columna ?j)     (fila ?y) (rango $?r3))
    (celda (columna ?j)     (fila ?z) (rango $?r4))
    (test (or 
            (and (member$ ?e $?r1) (member$ ?e $?r2)) 
            (and (member$ ?e $?r1) (member$ ?e $?r3)) 
            (and (member$ ?e $?r1) (member$ ?e $?r4)) 
            (and (member$ ?e $?r2) (member$ ?e $?r3)) 
            (and (member$ ?e $?r2) (member$ ?e $?r4)) 
            (and (member$ ?e $?r3) (member$ ?e $?r4))))
    (not (celda (columna ?j) (fila ?fila2&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;FILA3
    (celda (columna ?k&~?i&~?j) (fila ?w) (rango $?r5))
    (celda (columna ?k)         (fila ?x) (rango $?r6))
    (celda (columna ?k)         (fila ?y) (rango $?r7))
    (celda (columna ?k)         (fila ?z) (rango $?r8))
    (test (or 
            (and (member$ ?e $?r5) (member$ ?e $?r6)) 
            (and (member$ ?e $?r5) (member$ ?e $?r7)) 
            (and (member$ ?e $?r5) (member$ ?e $?r8)) 
            (and (member$ ?e $?r6) (member$ ?e $?r7)) 
            (and (member$ ?e $?r6) (member$ ?e $?r8)) 
            (and (member$ ?e $?r7) (member$ ?e $?r8))))
    (not (celda (columna ?k) (fila ?fila3&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;FILA4
    (celda (columna ?l&~?i&~?j&~?k) (fila ?w) (rango $?r9))
    (celda (columna ?l)             (fila ?x) (rango $?r10))
    (celda (columna ?l)             (fila ?y) (rango $?r11))
    (celda (columna ?l)             (fila ?z) (rango $?r12))
    (test (or 
            (and (member$ ?e $?r9) (member$ ?e $?r10)) 
            (and (member$ ?e $?r9) (member$ ?e $?r11)) 
            (and (member$ ?e $?r9) (member$ ?e $?r12)) 
            (and (member$ ?e $?r10) (member$ ?e $?r11)) 
            (and (member$ ?e $?r10) (member$ ?e $?r12)) 
            (and (member$ ?e $?r11) (member$ ?e $?r12))))
    (not (celda (columna ?l) (fila ?fila4&~?w&~?x&~?y&~?z) (rango $? ?e $?)))
    ;;Celda con candidato eliminable
    ?h1 <- (celda (columna ?columna&~?i&~?j&~?k&~?l) (fila ?fila&?w|?x|?y|?z) (rango $?a ?e $?b))
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-jellyfish* then (printout t "JellyFish COLUMNA filas(" ?w "," ?x "," ?y "," ?z ") y columnas(" ?i "," ?j "," ?k "," ?l ") para el candidato " ?e " sobre celda " ?fila "," ?columna crlf))
    (modify ?h1 (rango ?a ?b))
    (retract ?h0)
    (assert (estrategia-basica)))
    
;;; ===================================== Y-WING ============================================

;;; Y-Wing
;;;------------------------------------------------------------------------------------------------ 

(defrule y-wing
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (y-wing 1)
    ;PIVOTE
    (celda (fila ?fila1) (columna ?columna1) (caja ?caja1) (id ?id1) (rango ?e1 ?e2))
    ;WING 1
    (celda (fila ?fila2) (columna ?columna2) (caja ?caja2) (id ?id2&~?id1) (rango ?e1 ?e3))
    (test (comparten-visibilidad ?fila1 ?columna1 ?caja1 ?fila2 ?columna2 ?caja2)) ;;;el pivote debe ver a wing1
    ;WING 2
    (celda (fila ?fila3) (columna ?columna3) (caja ?caja3) (id ?id3&~?id1&~?id2) (rango ?e2 ?e3))
    (test (comparten-visibilidad ?fila1 ?columna1 ?caja1 ?fila3 ?columna3 ?caja3)) ;;;el pivote debe ver a wing2
    
    (test (not (comparten-visibilidad ?fila2 ?columna2 ?caja2 ?fila3 ?columna3 ?caja3))) ;;;Las alas no comparten visibilidad

    ?h0 <- (celda (fila ?fila4) (columna ?columna4) (caja ?caja4) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e3 $?b))
    (test (> (length (create$ ?a ?b)) 0))
    (test (and 
            (comparten-visibilidad ?fila4 ?columna4 ?caja4 ?fila2 ?columna2 ?caja2) ;;;el candidato debe ver a Wing1
            (comparten-visibilidad ?fila4 ?columna4 ?caja4 ?fila3 ?columna3 ?caja3))) ;;;el candidato debe ver a Wing2
    =>
    (if ?*informar-y-wing* then (printout t "Y-Wing en marcha,el pivote es: (" ?fila1 "," ?columna1 ")con rango:(" ?e1 "," ?e2 "). Wing1: (" ?fila2 "," ?columna2 "), con rango (" ?e1 "," ?e3 "). Wing2: (" ?fila3 "," ?columna3 ") con rango ("?e2 "," ?e3 "). Actuan sobre la celda (" ?fila4 "," ?columna4 ") eliminandole (" ?e3 ")" crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;; ===================================== XYZ-WING ============================================

;;; XYZ-Wing
;;;------------------------------------------------------------------------------------------------ 
(defrule xyz-wing
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (xyz-wing 1)
    (celda (fila ?fila1) (columna ?columna1) (caja ?caja1) (id ?id1) (rango $?rango&:(eq (length $?rango) 3)))  ;PIVOTE 
    (celda (fila ?fila2) (columna ?columna2) (caja ?caja2) (id ?id2&~?id1) (rango $?rango1&:(eq (length $?rango1) 2)));WING 1
    (test 
        (and
            (eq (length (interseccion2 $?rango $?rango1)) 2)
            (comparten-visibilidad ?fila1 ?columna1 ?caja1 ?fila2 ?columna2 ?caja2))) ;; Wing 1 ve a Pivote
    (celda (fila ?fila3) (columna ?columna3) (caja ?caja3) (id ?id3&~?id1&~?id2) (rango $?rango2&:(eq (length $?rango2) 2))) ;;; WING 2
    (test 
        (and
            (eq (length (interseccion2 $?rango2 $?rango)) 2)
            (eq (length (interseccion2 $?rango2 $?rango1)) 1) 
            (comparten-visibilidad ?fila1 ?columna1 ?caja1 ?fila3 ?columna3 ?caja3) ;; Wing 2 ve a Pivote
            (not (comparten-visibilidad ?fila2 ?columna2 ?caja2 ?fila3 ?columna3 ?caja3)))) ;; Wing 1 y Wing 2 no se ven
    ?h0 <- (celda (fila ?fila4) (columna ?columna4) (caja ?caja4) (id ?id4&~?id1&~?id2&~?id3) (rango $?a ?e1 $?b))
    (test 
        (and
            (member$ ?e1 (interseccion3 $?rango $?rango1 $?rango2)) ;;;es el elemento compartido por las alas
            (comparten-visibilidad ?fila4 ?columna4 ?caja4 ?fila1 ?columna1 ?caja1) ;;; el candidato debe ver a Pivote
            (comparten-visibilidad ?fila4 ?columna4 ?caja4 ?fila2 ?columna2 ?caja2) ;;;el candidato debe ver a Wing1
            (comparten-visibilidad ?fila4 ?columna4 ?caja4 ?fila3 ?columna3 ?caja3);;;el candidato debe ver a Wing2
            (> (length (create$ $?a $?b)) 0))) 
    =>
    (if ?*informar-xyz-wing* then (printout t "XYZ-Wing en marcha, PIVOTE: (" ?fila1 "," ?columna1 "). Wing1: (" ?fila2 "," ?columna2 "), con rango (" $?rango1 "). Wing2: (" ?fila3 "," ?columna3 ") con rango ("$?rango2 "). Actuan sobre la celda (" ?fila4 "," ?columna4 ") eliminandole (" ?e1 ")" crlf))
    (modify ?h0 (rango $?a $?b))             
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;; ===================================== WXYZ-WING ============================================

;;; WXYZ-Wing
;;;------------------------------------------------------------------------------------------------ 
(defrule wxyz-wing
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-avanzada)
    (wxyz-wing 1)
    (celda (fila ?fila1) (columna ?columna1) (caja ?caja1) (id ?id1) (rango $?rango&:(eq (length $?rango) 4)))  ;PIVOTE con 4 elementos 
    (celda (fila ?fila2) (columna ?columna2) (caja ?caja2) (id ?id2&~?id1) (rango $?rango1&:(eq (length $?rango1) 2)));WING 1   
    (test 
        (and
            (eq (length (interseccion2 $?rango $?rango1)) 2) 
            (comparten-visibilidad ?fila1 ?columna1 ?caja1 ?fila2 ?columna2 ?caja2))) 
    (celda (fila ?fila3) (columna ?columna3) (caja ?caja3) (id ?id3&~?id1&~?id2) (rango $?rango2&:(eq (length $?rango2) 2)))    ;WING 2 
    (test 
        (and
            (eq (length (interseccion2 $?rango2 $?rango)) 2)
            (eq (length (interseccion2 $?rango2 $?rango1)) 1)
            (comparten-visibilidad ?fila1 ?columna1 ?caja1 ?fila3 ?columna3 ?caja3))) ;
    (celda (fila ?fila4) (columna ?columna4) (caja ?caja4) (id ?id4&~?id1&~?id2&~?id3) (rango $?rango3&:(eq (length $?rango3) 2)))  ;WING 3
    (test 
        (and
            (eq (length (interseccion2 $?rango3 $?rango)) 2)
            (eq (length (interseccion2 $?rango3 $?rango1)) 1)
            (eq (length (interseccion2 $?rango3 $?rango2)) 1)
            (eq (length (interseccion3 $?rango1 $?rango2 $?rango3)) 1)
            (comparten-visibilidad ?fila1 ?columna1 ?caja1 ?fila4 ?columna4 ?caja4)))
    ?h0 <- (celda (fila ?fila5) (columna ?columna5) (caja ?caja5) (id ?id5&~?id1&~?id2&~?id3&~?id4) (rango $?a ?e1 $?b))
    (test (and 
        (member$ ?e1 (interseccion4 $?rango $?rango1 $?rango2 $?rango3))
        (comparten-visibilidad ?fila5 ?columna5 ?caja5 ?fila1 ?columna1 ?caja1) ;;; el candidato debe ver a Pivote
        (comparten-visibilidad ?fila5 ?columna5 ?caja5 ?fila2 ?columna2 ?caja2) ;;;el candidato debe ver a Wing1
        (comparten-visibilidad ?fila5 ?columna5 ?caja5 ?fila3 ?columna3 ?caja3);;;el candidato debe ver a Wing2
        (comparten-visibilidad ?fila5 ?columna5 ?caja5 ?fila4 ?columna4 ?caja4) ;;; el candidato debe ver a Wing3
        (> (length (create$ $?a $?b)) 0))) 
    =>
    (if ?*informar-wxyz-wing* then (printout t "WXYZ-Wing en marcha,pivote: (" ?fila1 "," ?columna1 "). Wing1: (" ?fila2 "," ?columna2 "). Wing2: (" ?fila3 "," ?columna3 ").Wing3: (" ?fila4 "," ?columna4 "). Actuan sobre la celda (" ?fila5 "," ?columna5 ") eliminandole (" ?e1 ")" crlf))
    (modify ?h0 (rango $?a $?b))
    (retract ?h1)
    (assert (estrategia-basica)))   

    
;;; ===================================== UNIQUE-RECTANGLES ============================================

;;;------------------------------------------------------------------------------------------------ 
;;; TIPO1
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo1-fila
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-unicidad)
    (unique-rectangles 1)
    (celda (fila ?i) (columna ?x) (caja ?c) (rango ?e1 ?e2)) ;;no le exijo valor 0 porque me aseguro que tenga 2 valores en el rango.
    (celda (fila ?i) (columna ?y&~?x) (caja ?c) (rango ?e1 ?e2))
    (celda (fila ?j&~?i) (columna ?x) (caja ?d&~?c) (rango ?e1 ?e2))
    ?h0 <- (celda (fila ?j) (columna ?y) (caja ?d) (rango ?a ?e1 ?b ?e2 ?c)) ;test de q tnga longitud 3 y q contenga a e1 y e2. en el modify le hacemos 
    (test (> (length (create$ ?a ?b ?c)) 0))
    =>
    (if ?*informar-unique-rectangles* then (printout t "Unique-rectangles en marcha: Esquina1 (" ?i "," ?x ") con rango:(" ?e1 "," ?e2 "). Esquina2(" ?i "," ?y "). Esquina3(" ?j "," ?x "). Esquina4(" ?j "," ?y "),con valor(" ?a "," ?b "," ?c ")," crlf))
    (modify ?h0 (rango ?a ?b ?c))
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;;------------------------------------------------------------------------------------------------ 
;;; TIPO2
;;;------------------------------------------------------------------------------------------------ 
    
;;; Fila
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo2-fila
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (fila ?i) (columna ?x) (caja ?c) (rango ?e1 ?e2) (id ?id1)) 
    (celda (fila ?i) (columna ?y) (caja ?c) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    (celda (fila ?j&~?i) (columna ?x) (caja ?d&~?c) (rango $?a ?e3&~?e1&~?e2 $?b) (id ?id3))
    (celda (fila ?j)     (columna ?y) (caja ?d)     (rango $?a ?e3 $?b)           (id ?id4&~?id3))
    (test (and 
            (= (length (create$ ?a ?b)) 2)
            (member$ ?e1 (create$ ?a ?b)) 
            (member$ ?e2 (create$ ?a ?b))))
               
    ;;ELIMINABLE
    (or
        ?h0 <- (celda (fila ?k&?j) (columna ?h) (rango $?a1 ?e3 $?b1) (id ?id5&~?id3&~?id4))
        ?h0 <- (celda (fila ?k) (columna ?h) (caja ?d) (rango $?a1 ?e3 $?b1) (id ?id5&~?id3&~?id4)))
    (test (> (length (create$ ?a1 ?b1)) 0))
    =>
    (if ?*informar-unique-rectangles* then (printout t "Unique Rectangles Tipo2 FILA (" ?e3 "). En la celda (" ?k "," ?h ")" crlf))
    (modify ?h0 (rango ?a1 ?b1))
    (retract ?h1)
    (assert (estrategia-basica)))

;;; Columna
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo2-columna
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (columna ?i) (fila ?x) (caja ?c) (rango ?e1 ?e2) (id ?id1)) 
    (celda (columna ?i) (fila ?y) (caja ?c) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    (celda (columna ?j&~?i) (fila ?x) (caja ?d&~?c) (rango $?a ?e3&~?e1&~?e2 $?b) (id ?id3))
    (celda (columna ?j)     (fila ?y) (caja ?d)     (rango $?a ?e3 $?b)           (id ?id4&~?id3))
    (test (and 
            (= (length (create$ ?a ?b)) 2)
            (member$ ?e1 (create$ ?a ?b)) 
            (member$ ?e2 (create$ ?a ?b))))
               
    ;;ELIMINABLE
    (or
        ?h0 <- (celda (columna ?k&?j) (fila ?h) (rango $?a1 ?e3 $?b1) (id ?id5&~?id3&~?id4))
        ?h0 <- (celda (columna ?k)    (fila ?h) (caja ?d) (rango $?a1 ?e3 $?b1) (id ?id5&~?id3&~?id4)))
    (test (> (length (create$ ?a1 ?b1)) 0))
    =>
    (if ?*informar-unique-rectangles* then (printout t "Unique Rectangles Tipo2 COLUMNA (" ?e3 "). En la celda (" ?h "," ?k ")" crlf))
    (modify ?h0 (rango ?a1 ?b1))
    (retract ?h1)
    (assert (estrategia-basica)))

;;;------------------------------------------------------------------------------------------------ 
;;; TIPO4
;;;------------------------------------------------------------------------------------------------ 
    
;;; FILA-VALOR1
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4-fila-valor1
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (fila ?i) (columna ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (fila ?i) (columna ?y) (caja ?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (fila ?j&~?i) (columna ?x) (caja ?d&~?caja) (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (fila ?j)     (columna ?y) (caja ?d)        (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))

    ;;CONDICION
    (or 
        (not (celda (fila ?j) (id ?id5&~?id3&~?id4) (rango $?a1 ?e1 $?b1)))
        (not (celda (caja ?d) (id ?id5&~?id3&~?id4) (rango $?a1 ?e1 $?b1))))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-fila. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e2  crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?e1 ?b ?c))
    (modify ?h1 (rango ?a ?e1 ?b ?c))
    (retract ?h2)
    (assert (estrategia-basica)))

;;; FILA-VALOR2
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4-fila-valor2
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (fila ?i) (columna ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (fila ?i) (columna ?y) (caja ?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (fila ?j&~?i) (columna ?x) (caja ?d&~?caja) (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (fila ?j)     (columna ?y) (caja ?d)        (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))

    ;;CONDICION
    (or 
        (not (celda (fila ?j) (id ?id5&~?id3&~?id4) (rango $?a1 ?e2 $?b1)))
        (not (celda (caja ?d) (id ?id5&~?id3&~?id4) (rango $?a1 ?e2 $?b1))))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-fila. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e1  crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?b ?e2 ?c))
    (modify ?h1 (rango ?a ?b ?e2 ?c))
    (retract ?h2)
    (assert (estrategia-basica)))

;;; COLUMA-VALOR1
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4-columna-valor1
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (columna ?i) (fila ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (columna ?i) (fila ?y) (caja ?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (columna ?j&~?i) (fila ?x) (caja ?d&~?caja) (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (columna ?j)     (fila ?y) (caja ?d)        (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))

    ;;ELIMINABLE
    (or 
        (not (celda (columna ?j) (id ?id5&~?id4&~?id3) (rango $?a1 ?e1 $?b1)))
        (not (celda (caja ?d) (id ?id5&~?id4&~?id3) (rango $?a1 ?e1 $?b1))))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-columna. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e2   crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?e1 ?b ?c))
    (modify ?h1 (rango ?a ?e1 ?b ?c))
    (retract ?h2)
    (assert (estrategia-basica)))

;;; COLUMA-VALOR2
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4-columna-valor2
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (columna ?i) (fila ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (columna ?i) (fila ?y) (caja ?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (columna ?j&~?i) (fila ?x) (caja ?d&~?caja) (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (columna ?j)     (fila ?y) (caja ?d)        (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))

    ;;ELIMINABLE
    (or 
        (not (celda (columna ?j) (id ?id5&~?id4&~?id3) (rango $?a1 ?e2 $?b1)))
        (not (celda (caja ?d) (id ?id5&~?id4&~?id3) (rango $?a1 ?e2 $?b1))))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-columna. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e1   crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?b ?e2 ?c))
    (modify ?h1 (rango ?a ?b ?e2 ?c))
    (retract ?h2)
    (assert (estrategia-basica)))
    
;;;------------------------------------------------------------------------------------------------ 
;;; TIPO4B
;;;------------------------------------------------------------------------------------------------ 
    
;;; FILA-VALOR1
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4b-fila-valor1
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (fila ?i) (columna ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (fila ?i) (columna ?y) (caja ?d&~?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (fila ?j&~?i) (columna ?x) (caja ?caja) (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (fila ?j)     (columna ?y) (caja ?d)   (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))
    (not (celda (fila ?j) (id ?id5&~?id3&~?id4) (rango $?a1 ?e1 $?b1)))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-fila. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e2  crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?e1 ?b ?c))
    (modify ?h1 (rango ?a ?e1 ?b ?c))
    (retract ?h2)
    (assert (estrategia-basica)))

;;; FILA-VALOR2
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4b-fila-valor2
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (fila ?i) (columna ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (fila ?i) (columna ?y) (caja ?d&~?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (fila ?j&~?i) (columna ?x) (caja ?caja) (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (fila ?j)     (columna ?y) (caja ?d)    (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))
    (not (celda (fila ?j) (id ?id5&~?id3&~?id4) (rango $?a1 ?e2 $?b1)))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-fila. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e1  crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?b ?e2 ?c))
    (modify ?h1 (rango ?a ?b ?e2 ?c))
    (retract ?h2)
    (assert (estrategia-basica)))

;;; COLUMA-VALOR1
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4b-columna-valor1
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (columna ?i) (fila ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (columna ?i) (fila ?y) (caja ?d&~?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (columna ?j&~?i) (fila ?x) (caja ?caja)     (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (columna ?j)     (fila ?y) (caja ?d)        (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))    
    (not (celda (columna ?j) (id ?id5&~?id4&~?id3) (rango $?a1 ?e1 $?b1)))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-columna. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e2   crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?e1 ?b ?c))
    (modify ?h1 (rango ?a ?e1 ?b ?c))
    (retract ?h2)
    (assert (estrategia-basica)))

;;; COLUMA-VALOR2
;;;------------------------------------------------------------------------------------------------ 
(defrule unique-rectangles-tipo4b-columna-valor2
    (estado ejecuta-estrategia)
    ?h2 <- (estrategia-unicidad)
    (unique-rectangles 1)
    ;;FLOOR
    (celda (columna ?i) (fila ?x) (caja ?caja) (rango ?e1 ?e2) (id ?id1)) 
    (celda (columna ?i) (fila ?y) (caja ?d&~?caja) (rango ?e1 ?e2) (id ?id2&~?id1))
    
    ;;ROOF
    ?h0 <- (celda (columna ?j&~?i) (fila ?x) (caja ?caja) (rango $?a ?e1 $?b ?e2 $?c) (id ?id3))
    ?h1 <- (celda (columna ?j)     (fila ?y) (caja ?d)        (rango $?a ?e1 $?b ?e2 $?c) (id ?id4&~?id3))
    (test (> (length (create$ ?a ?b ?c)) 0))
    (not (celda (columna ?j) (id ?id5&~?id4&~?id3) (rango $?a1 ?e2 $?b1)))
    =>
    (if ?*informar-unique-rectangles* 
        then 
        (printout t "Unique rectangles tipo4-columna. Las ROOF son: ROOF1(" ?j "," ?x ") ROOF2(" ?j "," ?y "), con elemento eliminable: " ?e1   crlf)
        (printout t "Rango ROOF's antes(" (create$ ?a ?e1 ?b ?e2 ?c) ")" crlf))
    (modify ?h0 (rango ?a ?b ?e2 ?c))
    (modify ?h1 (rango ?a ?b ?e2 ?c))
    (retract ?h2)
    (assert (estrategia-basica)))
    
    
;;; ===================================== EMPTY-RECTANGLES ============================================

;;;------------------------------------------------------------------------------------------------ 
;;; TIPO-FILA
;;;------------------------------------------------------------------------------------------------ 
(defrule empty-rectangles-fila
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-unicidad)
    (empty-rectangles 1)
    ;; Buscamos la celda ERI, esto es:
    (celda (fila ?i) (columna ?x) (id ?id_ERI) (caja ?c) (rango $? ?e1 $?)) ;;;ESTA SERÁ LA CELDA ERI
    (not (celda (fila ?j&~?i) (columna ?y&~?x) (caja ?c) (rango $? ?e1 $?))) ;;;Si no hay ninguna casilla en la caja con ?e1, restringiendo a que no compartan fila ni columna, forman el cuadrado vacío
    (celda (id ?id_OTRA&~id_ERI) (caja ?c) (rango $? ?e1 $?)) ;;; tiene que haber al menos 2 celdas con ese candidato en dicha caja.
    (celda (fila ?k&~?i) (columna ?x) (caja ?d&~?c) (rango $? ?e1 $?)) ;;;Extremo del enlace fuerte que comparte columna con nuestro ERI
    (celda (fila ?k) (columna ?z&~?x) (caja ?e&~?c) (rango $? ?e1 $?)) ;;; Extremo más lejano del enlace fuerte que va a determinar la interseccion con el ERI.
    (not (celda (fila ?k) (columna ?w&~?x&~?z) (rango $? ?e1 $?))) ;;; Condición de enlace fuerte en fila, solo ellos 2 van a tener el valor posible de ?e1
    ?h0 <- (celda (fila ?i) (columna ?z) (caja ?f&~?c) (rango $?a ?e1 $?b))   ;;; selecciono la casilla que es interseccion del ERI y el extremo lejano del enlace fuerte que ve el ERI, en este caso por columna.
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-empty-rectangles* then (printout t "Empty-Rectangles tipo-fila. ERI:(" ?i "," ?x "). EnlaceFuerte1:(" ?k "," ?x "). EnlaceFuerte2:(" ?k "," ?z "). Celda atacada:(" ?i "," ?z ")  con elemento eliminable: " ?e1 crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))
    
;;;------------------------------------------------------------------------------------------------ 
;;; TIPO-COLUMNA
;;;------------------------------------------------------------------------------------------------ 
    
(defrule empty-rectangles-columna
    (estado ejecuta-estrategia)
    ?h1 <- (estrategia-unicidad)
    (empty-rectangles 1)
    ;; Buscamos la celda ERI, esto es:
    (celda (columna ?i) (fila ?x) (id ?id_ERI) (caja ?c) (rango $? ?e1 $?)) ;;;ESTA SERÁ LA CELDA ERI
    (not (celda (columna ?j&~?i) (fila ?y&~?x) (caja ?c) (rango $? ?e1 $?))) ;;;Si no hay ninguna casilla en la caja con ?e1, restringiendo a que no compartan fila ni columna, forman el cuadrado vacío
    (celda (id ?id_OTRA&~id_ERI) (caja ?c) (rango $? ?e1 $?)) ;;; tiene que haber al menos 2 celdas con ese candidato en dicha caja.
    (celda (columna ?k&~?i) (fila ?x) (caja ?d&~?c) (rango $? ?e1 $?)) ;;;Extremo del enlace fuerte que comparte fila con nuestro ERI
    (celda (columna ?k) (fila ?z&~?x) (caja ?e&~?c) (rango $? ?e1 $?)) ;;; Extremo más lejano del enlace fuerte que va a determinar la interseccion con el ERI.
    (not (celda (columna ?k) (fila ?w&~?x&~?z) (rango $? ?e1 $?))) ;;; Condición de enlace fuerte en fila, solo ellos 2 van a tener el valor posible de ?e1
    ?h0 <- (celda (columna ?i) (fila ?z) (caja ?f&~?c) (rango $?a ?e1 $?b))   ;;; selecciono la casilla que es interseccion del ERI y el extremo lejano del enlace fuerte que ve el ERI, en este caso por columna.
    (test (> (length (create$ ?a ?b)) 0))
    =>
    (if ?*informar-empty-rectangles* then (printout t "Empty-Rectangles tipo-columna. ERI:(" ?x "," ?i "). EnlaceFuerte1:(" ?x "," ?k "). EnlaceFuerte2:(" ?z "," ?k "). Celda atacada:(" ?z "," ?i ")  con elemento eliminable: " ?e1  crlf))
    (modify ?h0 (rango ?a ?b))
    (retract ?h1)
    (assert (estrategia-basica)))