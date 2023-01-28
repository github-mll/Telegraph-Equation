
(* ===============================================================*)
(*                                                                *)
(*         Formalization of Telegrapher's Equations               *)
(*                                                                *)                                                               
(* ============================================================== *)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/cvectors.ml
needs "Multivariate/transcendentals.ml

let print_typed_var fmt tm =
      let s,ty = dest_var tm in
      pp_print_string fmt ("("^s^":"^string_of_type ty^")") in
    install_user_printer("print_typed_var",print_typed_var);;
    
(----For deleting type-----------)
delete_user_printer "print_typed_var";;

(*=================================================================*)
(*        Definitions of Telegrapher's Equations in Time Domain    *)
(*=================================================================*)

let telegraph_equation_voltage = new_definition
`telegraph_equation_voltage V (z,t) II (z,t) L <=> 
   (complex_derivative (\z. V (z,t)) z) = 
           -- (Cx L * complex_derivative (\t. II (z,t)) t)`;;

let telegraph_equation_current = new_definition
`telegraph_equation_current V (z,t) II (z,t) C <=> 
  (complex_derivative (\z. II (z,t)) z) = 
    -- (Cx C * complex_derivative (\t. V (z,t)) t)`;;

(*=================================================================*)
(*        Definitions of Wave Equations in Time Domain             *)
(*=================================================================*)

let wave_voltage_equation = new_definition `
    wave_voltage_equation V (z,t) L C <=> 
    higher_complex_derivative 2  (\z. V (z,t)) z = Cx L * Cx C *
    (higher_complex_derivative 2  (\t. V (z,t)) t)`;;

let wave_current_equation = new_definition `
    wave_current_equation II (z,t) L C = 
    higher_complex_derivative 2  (\z. II (z,t)) z = Cx L * Cx C *
    (higher_complex_derivative 2  (\t. II (z,t)) t)`;;

(*=================================================================*)
(*      Definitions of Telegrapher's Equations in Phasor Domain    *)
(*=================================================================*)

let telegraph_voltage = new_definition
`telegraph_voltage V II R L w z = complex_derivative (\z. V (z)) z 
                                = --(Cx R + ii * Cx w * Cx L) * II (z)`;;


let telegraph_current_phasor = new_definition
`telegraph_current_phasor V II G C w z =  
       complex_derivative (\z. II (z)) z = --(Cx G + ii * Cx w * Cx C) * V (z)`;;

ALTERNATE DEFINITIONS

let telegraph_voltage_phasor = new_definition
`telegraph_voltage_phasor V II R L w z = 
      complex_derivative (\z. V (z)) z + (Cx R + ii * Cx w * Cx L) * II (z)`;;

Let telegraph_voltage_equation_phasor = new_definition
`telegraph_voltage_equation_phasor V II R L w z  <=> 
    telegraph_voltage_phasor V II R L w z = Cx (&0)`;; 

let telegraph_current_phasor = new_definition
`telegraph_current_phasor V II G C w z = 
   complex_derivative (\z. II (z)) z + (Cx G + ii * Cx w * Cx C) * V (z)`;;

let telegraph_current_equation_phasor = new_definition
`telegraph_current_equation_phasor V II G C w z  <=> 
   telegraph_current_phasor V II G C w z = Cx (&0)`;;

(*=================================================================*)
(*      Definitions of Wave Equations in Phasor Domain             *)
(*=================================================================*)

let propagation_constant = new_definition `propagation_constant R L G C w
                         = csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C))`;;

let wave_voltage = new_definition `
    wave_voltage V z R L G C w =
    higher_complex_derivative 2  V (z) = (propagation_constant R L G C w) pow 2 * V (z)`;;

let wave_current_phasor = new_definition `
    wave_current_phasor II z R L G C w = 
    higher_complex_derivative 2  II (z) = (propagation_constant R L G C w) pow 2 * II (z)`;;

ALTERNATE DEFINITIONS

let wave_voltage_phasor = new_definition `
    wave_voltage_phasor V z R L G C w =
    higher_complex_derivative 2  V (z) -(propagation_constant R L G C w) pow 2 * V (z)`;;

let wave_voltage_equation_phasor = new_definition
`wave_voltage_equation_phasor V z R L G C w = wave_voltage_phasor V z R L G C w = Cx (&0)`;;

let wave_current_phasor = new_definition `
    wave_current_phasor II z R L G C w = 
    higher_complex_derivative 2  II (z) -(propagation_constant R L G C w) pow 2 * II (z)`;;

let wave_current_equation_phasor = new_definition
`wave_current_equation_phasor II z R L G C w = wave_current_phasor II z R L G C w = Cx (&0)`;; 

(*=======================================================================================*)
(*    Relationship between Telegrapher's and Wave Equations in Phasor Domain             *)
(*=======================================================================================*)

1) g `!V z R L G C w. (\z. complex_derivative V z) complex_differentiable at z /\
 (\z. (Cx R + ii * Cx w * Cx L) * II z) complex_differentiable at z /\
 I complex_differentiable at z /\ telegraph_current V I G C w z = Cx (&0)
     ==> complex_derivative (\z. telegraph_voltage_phasor V II R L w z) z 
             = wave_voltage_phasor V z R L G C w`;;

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC[telegraph_voltage_phasor;wave_voltage_phasor]);;
e (REWRITE_TAC [ARITH_RULE `2 = SUC 1`]);;
e (REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1]);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC[telegraph_current]);;
e (DISCH_TAC);;
e (SUBGOAL_THEN `complex_derivative
 (\z. complex_derivative V z + (Cx R + ii * Cx w * Cx L) * II z)
 z = complex_derivative (\z. complex_derivative V z) z + 
   complex_derivative (\z. (Cx R + ii * Cx w * Cx L) * II z) z` ASSUME_TAC);;
e (MATCH_MP_TAC COMPLEX_DERIVATIVE_ADD);;
e (ASM_SIMP_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `complex_derivative (\z. (Cx R + ii * Cx w * Cx L) * I z) z 
        = (Cx R + ii * Cx w * Cx L) * complex_derivative I z` ASSUME_TAC);;
e (MATCH_MP_TAC COMPLEX_DERIVATIVE_LMUL);;
e (ASM_SIMP_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (UNDISCH_TAC `complex_derivative I z + (Cx G + ii * Cx w * Cx C) * V z = Cx (&0)`);;
e (REWRITE_TAC[COMPLEX_FIELD `complex_derivative I z + (Cx G + ii * Cx w * Cx C) * V z = Cx (&0)
                 <=> complex_derivative I z = -- (Cx G + ii * Cx w * Cx C) * V z`]);;
e (DISCH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[ETA_AX]);;
e (SIMP_TAC[COMPLEX_FIELD `complex_derivative (complex_derivative V) z +
 (Cx R + ii * Cx w * Cx L) * --(Cx G + ii * Cx w * Cx C) * V z = complex_derivative (complex_derivative V) z -
 (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) * V z`]);;

let TELEGRAPH_WAVE_RELATIONSHIP_1 = top_thm ();;

2) g `!V z R L G C w. (\z. complex_derivative I z) complex_differentiable at z /\
 (\z. (Cx G + ii * Cx w * Cx C) * V z) complex_differentiable at z /\
 V complex_differentiable at z /\ telegraph_voltage V I R L w z = Cx (&0)
 ==> complex_derivative (\z. telegraph_current_phasor V I G C w z) z = wave_current_phasor I z R L G C w`;;

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC[telegraph_current_phasor;wave_current_phasor]);;
e (REWRITE_TAC [ARITH_RULE `2 = SUC 1`]);;
e (REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1]);;
e (POP_ASSUM MP_TAC);;
e (REWRITE_TAC[telegraph_voltage]);;
e (DISCH_TAC);;
e (SUBGOAL_THEN `complex_derivative (\z. complex_derivative I z + (Cx G + ii * Cx w * Cx C) * V z)
 z = complex_derivative (\z. complex_derivative I z) z + complex_derivative (\z. (Cx G + ii * Cx w * Cx C) * V z)
 z` ASSUME_TAC);;
e (MATCH_MP_TAC COMPLEX_DERIVATIVE_ADD);;
e (ASM_SIMP_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (SUBGOAL_THEN `complex_derivative (\z. (Cx G + ii * Cx w * Cx C) * V z) z 
= (Cx G + ii * Cx w * Cx C) * complex_derivative V z` ASSUME_TAC);;
e (MATCH_MP_TAC COMPLEX_DERIVATIVE_LMUL);;
e (ASM_SIMP_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (UNDISCH_TAC `complex_derivative V z + (Cx R + ii * Cx w * Cx L) * II z = Cx (&0)`);;
e (REWRITE_TAC[COMPLEX_FIELD `complex_derivative V z + (Cx R + ii * Cx w * Cx L) * II z = Cx (&0)
 <=> complex_derivative V z = -- (Cx R + ii * Cx w * Cx L) * I z`]);;
e (DISCH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[ETA_AX]);;
e (SIMP_TAC[COMPLEX_FIELD `complex_derivative (complex_derivative I) z +
 (Cx G + ii * Cx w * Cx C) * --(Cx R + ii * Cx w * Cx L) * II z = complex_derivative (complex_derivative II) z -
 (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) * II z`]);;

let TELEGRAPH_WAVE_RELATIONSHIP_2 = top_thm ();;

(*=================================================================*)
(*     Proof of Attenuation and Phase Coefficient                  *)
(*=================================================================*)

g `&0 < Re ii \/ Re ii = &0 /\ &0 <= Im ii  ==> csqrt (--Cx(&1)) = ii`;;

e (REPEAT DISCH_TAC);;
e (ASSERT_TAC `csqrt (ii pow 2) = ii`);;
e (MATCH_MP_TAC POW_2_CSQRT);;
e (ASM_SIMP_TAC[]);;
e (ASSERT_TAC `ii pow 2 = --Cx(&1)`);;
e(REWRITE_TAC[COMPLEX_POW_II_2]);;
e (ASM_MESON_TAC[]);;

let CSQRT_MINUS = top_thm();;

 g `!R L G C w.  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
 ==>  &0 < Re ii \/ Re ii = &0 /\ &0 <= Im ii
   ==> Re (propagation_constant R L G C w) = &0`;;

e (REPEAT GEN_TAC);;
e (REPEAT DISCH_TAC);;
e (REWRITE_TAC[propagation_constant]);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_ADD_LID]);;
e (REWRITE_TAC [COMPLEX_FIELD `(ii * Cx w * Cx L) * ii * Cx w * Cx C = (Cx w) * (Cx w) * Cx L * Cx C * ii pow 2`]);;
e (ASSERT_TAC `Cx w * Cx w * Cx L * Cx C * ii pow 2 = Cx (w * w * L * C) * ii pow 2`);;
 e (REWRITE_TAC[CX_MUL]);;
 e (SIMPLE_COMPLEX_ARITH_TAC);;
 e (ASM_REWRITE_TAC[]);;
 e (ASSERT_TAC `Cx(w * w * L * C) = Cx (w pow 2 * L * C)`);;
 e (SIMPLE_COMPLEX_ARITH_TAC);;
 e (ASM_REWRITE_TAC[]);;
 e (ASSERT_TAC `csqrt (Cx (w pow 2 * L * C) * ii pow 2) = Cx(sqrt (w pow 2 * L * C)) * csqrt (ii pow 2)`);;
 e (MATCH_MP_TAC CSQRT_MUL_LCX);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (CONJ_TAC);;
e (REWRITE_TAC[REAL_POW_2]);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (ASSERT_TAC `Cx(sqrt (w pow 2 * L * C)) = csqrt(Cx (w pow 2 * L * C))`);;
e (MATCH_MP_TAC CX_SQRT);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (CONJ_TAC);;
e (REWRITE_TAC[REAL_POW_2]);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC [COMPLEX_POW_II_2]);;
e (ASSERT_TAC `csqrt (--Cx (&1)) = ii`);;
e (MATCH_MP_TAC CSQRT_MINUS);;
e (ASM_SIMP_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (ASSERT_TAC `Re (csqrt (Cx (w pow 2 * L * C)) * ii) = Re (ii * csqrt (Cx (w pow 2 * L * C)))`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[RE_MUL_II]);;
e (ASSERT_TAC `csqrt(Cx (w pow 2 * L * C)) = Cx(sqrt (w pow 2 * L * C))`);;
e (MATCH_MP_TAC CSQRT_CX);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (CONJ_TAC);;
e (REWRITE_TAC[REAL_POW_2]);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[IM_CX]);;
e (ASM_REAL_ARITH_TAC);;

let PROPAGATION_CONSTANT_REAL = top_thm();;

 g `!R L G C w.  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
 ==>  &0 < Re ii \/ Re ii = &0 /\ &0 <= Im ii
   ==> Im (propagation_constant R L G C w) = w * sqrt(L * C)`;;

e (REPEAT GEN_TAC);;
e (REPEAT DISCH_TAC);;
e (REWRITE_TAC[propagation_constant]);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_ADD_LID]);;
e (REWRITE_TAC [COMPLEX_FIELD `(ii * Cx w * Cx L) * ii * Cx w * Cx C = (Cx w) * (Cx w) * Cx L * Cx C * ii pow 2`]);;
e (ASSERT_TAC `Cx w * Cx w * Cx L * Cx C * ii pow 2 = Cx (w * w * L * C) * ii pow 2`);;
 e (REWRITE_TAC[CX_MUL]);;
 e (SIMPLE_COMPLEX_ARITH_TAC);;
 e (ASM_REWRITE_TAC[]);;
 e (ASSERT_TAC `Cx(w * w * L * C) = Cx (w pow 2 * L * C)`);;
 e (SIMPLE_COMPLEX_ARITH_TAC);;
 e (ASM_REWRITE_TAC[]);;
 e (ASSERT_TAC `csqrt (Cx (w pow 2 * L * C) * ii pow 2) = Cx(sqrt (w pow 2 * L * C)) * csqrt (ii pow 2)`);;
 e (MATCH_MP_TAC CSQRT_MUL_LCX);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (CONJ_TAC);;
e (REWRITE_TAC[REAL_POW_2]);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (ASSERT_TAC `Cx(sqrt (w pow 2 * L * C)) = csqrt(Cx (w pow 2 * L * C))`);;
e (MATCH_MP_TAC CX_SQRT);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (CONJ_TAC);;
e (REWRITE_TAC[REAL_POW_2]);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC [COMPLEX_POW_II_2]);;
e (ASSERT_TAC `csqrt (--Cx (&1)) = ii`);;
e (MATCH_MP_TAC CSQRT_MINUS);;
e (ASM_SIMP_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (ASSERT_TAC `csqrt(Cx (w pow 2 * L * C)) = Cx(sqrt (w pow 2 * L * C))`);;
e (MATCH_MP_TAC CSQRT_CX);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (CONJ_TAC);;
e (REWRITE_TAC[REAL_POW_2]);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[IM_MUL_II]);;
e (REWRITE_TAC[RE_CX]);;
e (REWRITE_TAC[SQRT_MUL]);;
e (ASSERT_TAC `sqrt (w pow 2) = w`);;
e (REWRITE_TAC[REAL_POW_2]);;
e (REWRITE_TAC[SQRT_MUL]);;
e (REWRITE_TAC[REAL_FIELD `sqrt w * sqrt w = sqrt (w) pow 2`]);;
e (MATCH_MP_TAC SQRT_POW_2);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REAL_ARITH_TAC);;

let PROPAGATION_CONSTANT_IMAGINARY = top_thm();;

(*=================================================================*)
(* General Solution of Wave Equation for Voltage in Phasor Domain  *)
(*=================================================================*)

let wave_solution_voltage_phasor = new_definition `wave_solution_voltage_phasor1 
 (V1:complex) (V2:complex) (R:real)(L:real) (G:real) (C:real) (w:real) (z:complex) = 
                V1 * cexp (--(propagation_constant R L G C w) * z) + 
                 V2 * cexp ((propagation_constant R L G C w) * z)`;;

1) g `!(V1:complex) (V2:complex) (R:real) (C:real) (L:real) (G:real) (w:real) (z:complex). 
complex_derivative (\z. wave_solution_voltage_phasor V1 V2 R L G C w z) z =
V1 * (--(propagation_constant R L G C w)) * cexp (--(propagation_constant R L G C w) * z) + 
V2 * (propagation_constant R L G C w) * cexp ((propagation_constant R L G C w) * z)`;;

e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE);;
e (REWRITE_TAC [wave_solution_voltage_phasor;propagation_constant]);;
e (COMPLEX_DIFF_TAC);;
e (REWRITE_TAC[COMPLEX_MUL_RID]);;

let WAVE_VOLTAGE_1 = top_thm ();;

2) g `!(V1:complex) (V2:complex) (R:real) (C:real) (L:real) (G:real) (w:real) (z:complex). 
complex_derivative (\z. wave_solution_voltage_phasor V1 V2 R C L G w z)  = 
(\z.  V1 * --(propagation_constant R L G C w) * cexp (--(propagation_constant R L G C w) * z) +
 V2 * (propagation_constant R L G C w) * cexp ((propagation_constant R L G C w) * z))`;;

e (REWRITE_TAC[FUN_EQ_THM]);;
e (MESON_TAC[WAVE_VOLTAGE_1;propagation_constant]);;

let WAVE_VOLTAGE_2 = top_thm ();;

3) g `!(V1:complex) (V2:complex) (R:real) (C:real) (L:real) (G:real) (w:real) (z:complex). 
 complex_derivative (\z. V1 * --(propagation_constant R L G C w) * cexp (--(propagation_constant R L G C w) * z) +
  V2 * (propagation_constant R L G C w) * cexp ((propagation_constant R L G C w) * z) z =
   V1 * (propagation_constant R L G C w) pow 2 * cexp (--(propagation_constant R L G C w) * z) +
    V2 * (propagation_constant R L G C w) pow 2 * cexp ((propagation_constant R L G C w) * z)`;;

e (REPEAT STRIP_TAC THEN REWRITE_TAC[propagation_constant; CSQRT] 
THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN COMPLEX_DIFF_TAC);;
e (REWRITE_TAC[COMPLEX_MUL_RID]);;

e (REWRITE_TAC[COMPLEX_FIELD `V1 *
 --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
 V2 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) = V1 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
 V2 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)`]);;

e (REWRITE_TAC[COMPLEX_FIELD `V1 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
 V2 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) = V1 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2 *
 cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
 V2 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2 *
 cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)`]);;

e (REWRITE_TAC[CSQRT]);;

let WAVE_VOLTAGE_3 = top_thm ();;

4) g `!(V1:complex) (V2:complex) (R:real) (C:real) (L:real) (G:real) (w:real) (z:complex). 
higher_complex_derivative 2 (\z. wave_solution_voltage_phasor V1 V2 R C L G w z) z = 
V1 * (propagation_constant R L G C w) pow 2 * cexp (--(propagation_constant R L G C w) * z) + 
V2 * (propagation_constant R L G C w) pow 2 * cexp ((propagation_constant R L G C w) * z)`;;

e (SIMP_TAC [ARITH_RULE `2 = SUC 1`]);;
e (REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1]);;
e (REWRITE_TAC[propagation_constant;CSQRT]);;
e (SIMP_TAC [ARITH_RULE `SUC 1 = 2`]);;
e (REWRITE_TAC [WAVE_VOLTAGE_2]);;
e (SIMP_TAC[WAVE_VOLTAGE_3]);;
e (REWRITE_TAC[propagation_constant;CSQRT]);;

let WAVE_VOLTAGE_4 = top_thm ();;

5) g `!V1 V2 R C L G w z. (wave_voltage_equation_phasor (\z. wave_solution_voltage_phasor V1 V2 R C L G w z) (z) R L G C w)`;;

e (REWRITE_TAC[wave_voltage_equation_phasor; wave_voltage_phasor]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC[WAVE_VOLTAGE_4]);;
e (REWRITE_TAC[wave_solution_voltage_phasor;propagation_constant;CSQRT]);;
e (REWRITE_TAC[COMPLEX_FIELD `(V1 *
  ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
  V2 *
  ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) = 
((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * (V1 * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +  
V2 * (cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)))`]);;
e (REWRITE_TAC[COMPLEX_SUB_0]);;
e (REWRITE_TAC[COMPLEX_FIELD `((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
 (V1 *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
  V2 * cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) = 
  (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
 (V1 * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
  V2 * cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))`]);;

let WAVE_SOLUTION_VOLTAGE_PHASOR_VERIFIED = top_thm ();;

(*=================================================================*)
(* General Solution of Wave Equation for Current in Phasor Domain  *)
(*=================================================================*)

let wave_solution_current_phasor =
new_definition `wave_solution_current_phasor V1 V2 R L G C w z =
 propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) * 
(V1 * cexp (-- (propagation_constant R L G C w) * z) - V2 * cexp ((propagation_constant R L G C w) * z))`;;

1) let WAVE_CURRENT_1 = prove (`!V1 V2 R L G C w z. complex_derivative (\z. wave_solution_current_phasor V1 V2 R L G C w z ) z = 
propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) * (V1 * (--propagation_constant R L G C w) * 
cexp (--(propagation_constant R L G C w) * z) - 
V2 * (propagation_constant R L G C w) * cexp ((propagation_constant R L G C w) * z))`, 

REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  REWRITE_TAC [wave_solution_current_phasor;propagation_constant] THEN COMPLEX_DIFF_TAC
THEN REWRITE_TAC[COMPLEX_MUL_RID]);;

2) let WAVE_CURRENT_2 = prove (`!V1 V2 R L G C w z. complex_derivative (\z. wave_solution_current_phasor V1 V2 R L G C w z )  = 
(\z. propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) *
 (V1 * (--propagation_constant R L G C w) * cexp (--(propagation_constant R L G C w) * z) - 
 V2 * (propagation_constant R L G C w * cexp ((propagation_constant R L G C w) * z))))`,

REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [WAVE_CURRENT_1]);;

3) let WAVE_CURRENT_3 = prove (`!V1 V2 R L G C w z. complex_derivative (\z. propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) *
 (V1 * --propagation_constant R L G C w * cexp (--(propagation_constant R L G C w) * z) - 
 V2 * propagation_constant R L G C w * cexp ((propagation_constant R L G C w) * z))) z

= propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) * (V1 * (propagation_constant R L G C w) pow 2 * 
cexp (--(propagation_constant R L G C w) * z) - V2 * (propagation_constant R L G C w) pow 2 * cexp ((propagation_constant R L G C w) * z))`,

REPEAT STRIP_TAC THEN REWRITE_TAC[propagation_constant; CSQRT] 
THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN COMPLEX_DIFF_TAC 
THEN REWRITE_TAC[COMPLEX_MUL_RID] THEN 
REWRITE_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) *
 (V1 *
  --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) 
  = csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) *
 (V1 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))`] THEN  

REWRITE_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) *
 (V1 *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) = 
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) *
 (V1 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2 *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2
  * cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))`] 
  THEN SIMP_TAC[CSQRT] THEN REWRITE_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) *
 (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) = 
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) * (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))`]);;


4) let WAVE_CURRENT_4 = prove (`!V1 V2 R L G C w z. higher_complex_derivative 2 (\z. wave_solution_current_phasor V1 V2 R L G C w z ) z 
= propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) *
 (V1 * (propagation_constant R L G C w) pow 2 * cexp (--(propagation_constant R L G C w) * z) - 
 V2 * (propagation_constant R L G C w) pow 2 * cexp ((propagation_constant R L G C w) * z))`,

SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN
  REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1] THEN REWRITE_TAC[propagation_constant;CSQRT] THEN
  REWRITE_TAC [WAVE_CURRENT_2] THEN REWRITE_TAC [WAVE_CURRENT_3] THEN REWRITE_TAC[propagation_constant;CSQRT] THEN
 SIMP_TAC [ARITH_RULE `SUC 1 = 2 `] THEN REWRITE_TAC [propagation_constant;CSQRT]);;

5) g `!V1 V2 R C L G w z. (wave_current_equation_phasor (\z. wave_solution_current_phasor V1 V2 R L G C w z) (z) R L G C w)`;;

e (REWRITE_TAC[wave_current_equation_phasor; wave_current_phasor; WAVE_CURRENT_4; wave_solution_current_phasor]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC[propagation_constant;CSQRT]);;
e (REWRITE_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) * (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) * 
 cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) -
 (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) *
 (V1 * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) =
 Cx (&0) <=> csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) * (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))  =
 (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) *
 (V1 * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))
`]);;

e (CONV_TAC COMPLEX_FIELD);;

let WAVE_SOLUTION_CURRENT_PHASOR_VERIFIED = top_thm();;

(*============================================================================================*)
(* General Solutions of Wave Equations also satisfy Telegrapher's Equations in Phasor Domain  *)
(*============================================================================================*)

g `!V1 V2 R C L G w z II V.  ~(Cx R + ii * Cx w * Cx L = Cx (&0)) /\
 (!z. V z = wave_solution_voltage_phasor V1 V2 R L G C w z) /\
 (!z. II z = wave_solution_current_phasor V1 V2 R L G C w z)
        ==> telegraph_voltage_equation_phasor V II R L w z`;;

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC[telegraph_voltage_equation_phasor;telegraph_voltage_phasor]);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[WAVE_VOLTAGE_1;wave_solution_current_phasor]);;
e (REWRITE_TAC[COMPLEX_FIELD `(V1 *
  --propagation_constant R L G C w *
  cexp (--propagation_constant R L G C w * z) +
  V2 *
  propagation_constant R L G C w *
  cexp (propagation_constant R L G C w * z)) +
 (Cx R + ii * Cx w * Cx L) *
 propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) *
 (V1 * cexp (--propagation_constant R L G C w * z) -
  V2 * cexp (propagation_constant R L G C w * z)) =
 Cx (&0) <=> (V1 *
  --propagation_constant R L G C w *
  cexp (--propagation_constant R L G C w * z) +
  V2 *
  propagation_constant R L G C w *
  cexp (propagation_constant R L G C w * z)) +
 ((Cx R + ii * Cx w * Cx L) *
 propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L)) *
 (V1 * cexp (--propagation_constant R L G C w * z) -
  V2 * cexp (propagation_constant R L G C w * z)) =
 Cx (&0)`]);;

e (SUBGOAL_THEN `(Cx R + ii * Cx w * Cx L) * propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) 
   = propagation_constant R L G C w` ASSUME_TAC);;
e (MATCH_MP_TAC COMPLEX_DIV_LMUL);;
e (ASM_SIMP_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_FIELD `!(a:complex) (b:complex). a + b = Cx(&0) <=> a = --b`]);;
e (REWRITE_TAC[COMPLEX_SUB_LDISTRIB]);;
e (REWRITE_TAC[COMPLEX_FIELD `!(a:complex) (b:complex). --(a - b) = --a + b`]);;
e (REWRITE_TAC[COMPLEX_FIELD `!(a:complex) (b:complex) (c:complex). --(a * b * c) = --a * b * c`])
e (SIMPLE_COMPLEX_ARITH_TAC);;

let WAVESOL_FOR_TELEG_VOLTAGE = top_thm();;

(*=================================================================*)
(* Relations Between Time and Phasor Domain Expressions            *)
(*=================================================================*)

let wave_solution_voltage_time = new_definition `wave_solution_voltage_time (V1:complex) (V2:complex) (R:real) (C:real) 
(L:real) (G:real) (w:real) (z:complex) (t:complex) = 
                       Re((wave_solution_voltage_phasor V1 V2 R C L G w z) * cexp(ii * Cx w * t))`;;

let wave_solution_current_time = new_definition `wave_solution_current_time (V1:complex) (V2:complex) (R:real) (C:real) (L:real) (G:real) 
(w:real) (z:complex) (t:complex) = Re((wave_solution_current_phasor V1 V2 R L G C w z) * cexp(ii * Cx w * t))`;;


g `!R L G C w. complex (Re (propagation_constant R L G C w) , Im (propagation_constant R L G C w)) = propagation_constant R L G C w`;;

e (MESON_TAC[COMPLEX]);;

let PROPAGATION_CONSTANT_COMPLEX = top_thm();;

g `!x y. Re(Cx(x) + ii * Cx(y)) = x`;;
e (REWRITE_TAC[ii]);;
e(SIMPLE_COMPLEX_ARITH_TAC);;

let REAL_COMPLEX_1 = top_thm();;

g `!R L G C w.  complex (Re(propagation_constant R L G C w) , Im(propagation_constant R L G C w)) = 
Cx(Re(propagation_constant R L G C w)) + ii * Cx(Im(propagation_constant R L G C w))`;;

e (MESON_TAC[COMPLEX_TRAD]);;

let PROPAGATION_CONSTANT_COMPLEX_TRAD = top_thm();;

g `!V1 V2 R C L G z w t. &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
==> &0 < Re ii \/ Re ii = &0 /\ &0 <= Im ii
==> wave_solution_voltage_time V1 V2 R C L G w z t =
Re(V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant R L G C w)) * z)) +
V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant R L G C w)) * z)))`;;

e (REPEAT GEN_TAC);;
e (REPEAT DISCH_TAC);;
e (REWRITE_TAC[wave_solution_voltage_time;wave_solution_voltage_phasor]);;
e (ONCE_ASM_REWRITE_TAC[GSYM PROPAGATION_CONSTANT_COMPLEX]);;
e (ONCE_ASM_REWRITE_TAC[PROPAGATION_CONSTANT_COMPLEX_TRAD]);;
e (REWRITE_TAC[COMPLEX_ADD_RDISTRIB]);;
e (ASM_SIMP_TAC[PROPAGATION_CONSTANT_REAL1]);;
e (REWRITE_TAC[COMPLEX_MUL_LZERO]);;
e (REWRITE_TAC[COMPLEX_ADD_LID]);;
e (ASSERT_TAC `(V1 * cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)) *
  cexp (ii * Cx w * t) = (V1 * cexp (ii * Cx w * t) * cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z))`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (ASSERT_TAC `(V2 * cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)) * cexp (ii * Cx w * t) = 
(V2 * cexp (ii * Cx w * t) * cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z))`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[GSYM CEXP_ADD]);;
e (REWRITE_TAC[IM_MUL_II;RE_CX]);;
e (REWRITE_TAC[COMPLEX_FIELD `ii * Cx w * t + --(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z = 
 ii * Cx w * t - (ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z`]);;
e (REWRITE_TAC[COMPLEX_FIELD `ii * Cx w * t - (ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z = 
 ii * (Cx w * t - (Cx (Im (propagation_constant (&0) L (&0) C w)) * z))`]);;
e (REWRITE_TAC[GSYM COMPLEX_MUL_LNEG]);;
e (REWRITE_TAC[COMPLEX_FIELD `Cx w * t + --Cx (Im (propagation_constant (&0) L (&0) C w)) * z = 
Cx w * t - Cx (Im (propagation_constant (&0) L (&0) C w)) * z`]);;
e (REWRITE_TAC[COMPLEX_FIELD `ii * Cx w * t + (ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z = 
ii * (Cx w * t + Cx (Im (propagation_constant (&0) L (&0) C w)) * z)`]);;

let WAVE_VOLTAGE_TIME_1 = top_thm();;

g `!V1 V2 R C L G z w t. &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
==> &0 < Re ii \/ Re ii = &0 /\ &0 <= Im ii
==> wave_solution_current_time V1 V2 R C L G w z t = 
Re(propagation_constant R L G C w / (Cx R + ii * Cx w * Cx L) *
 (V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant R L G C w)) * z)) -
V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant R L G C w)) * z))))`;;

e (REPEAT GEN_TAC);;
e (REPEAT DISCH_TAC);;
e (REWRITE_TAC[wave_solution_current_time;wave_solution_current_phasor]);;
e (ONCE_ASM_REWRITE_TAC[GSYM PROPAGATION_CONSTANT_COMPLEX]);;
e (ONCE_ASM_REWRITE_TAC[PROPAGATION_CONSTANT_COMPLEX_TRAD]);;
e (REWRITE_TAC[COMPLEX_SUB_RDISTRIB; COMPLEX_SUB_LDISTRIB]);;
e (ASM_SIMP_TAC[PROPAGATION_CONSTANT_REAL]);;
e (REWRITE_TAC[COMPLEX_MUL_LZERO]);;
e (REWRITE_TAC[COMPLEX_ADD_LID]);;
e (ASSERT_TAC `Re
 (((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
   V1 *
   cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)) *
  cexp (ii * Cx w * t) -
  ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
   V2 *
   cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)) *
  cexp (ii * Cx w * t)) = Re
 ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
   V1 *
   cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z) *
  cexp (ii * Cx w * t) -
  ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
   V2 *
   cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)) *
  cexp (ii * Cx w * t))`);;

e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_FIELD `V1 *
  cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z) *
  cexp (ii * Cx w * t) = V1 * cexp (ii * Cx w * t) * cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)`]);;
  
e (ASSERT_TAC `Re
 ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
  V1 *
  cexp (ii * Cx w * t) *
  cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z) -
  ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
   V2 *
   cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)) *
  cexp (ii * Cx w * t)) = Re
 ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
  V1 *
  cexp (ii * Cx w * t) *
  cexp (--(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z) -
  (ii * Cx (Im (propagation_constant (&0) L (&0) C w))) / (ii * Cx w * Cx L) *
   V2 *
   cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z) *
  cexp (ii * Cx w * t))`);;
  
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_FIELD `V2 *
  cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z) *
  cexp (ii * Cx w * t) = V2 * cexp (ii * Cx w * t) * 
  cexp ((ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z)`]);;

e (REWRITE_TAC[GSYM CEXP_ADD]);;
e (REWRITE_TAC[IM_MUL_II;RE_CX]);;
e (REWRITE_TAC[COMPLEX_FIELD `ii * Cx w * t + --(ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z = 
ii * Cx w * t - ii * Cx (Im (propagation_constant (&0) L (&0) C w)) * z`]);;
e (REWRITE_TAC[COMPLEX_FIELD `ii * Cx w * t + (ii * Cx (Im (propagation_constant (&0) L (&0) C w))) * z = 
ii * (Cx w * t + (Cx (Im (propagation_constant (&0) L (&0) C w)) * z))`]);;

let WAVE_CURRENT_TIME_1 = top_thm();;

(*=================================================================*)
(*                   End of Formalization                          *)
(*=================================================================*)
