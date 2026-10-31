import Langlands.Global.ArchimedeanCartanPolynomialCoefficientAnalyticity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Fintype.BigOperators

/-! # Action correctness for the explicit Cartan coefficient recurrence -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator ContDiff
open Set Filter Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private def cartanArrayAction {r : ℕ} (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) (x : ArchimedeanMatrix K n) : ℂ :=
  ∑ k : Fin (r + 1), ∑ w : Fin k.val → Fin (cartanCoordinateDimension K n),
    a k w x * iteratedFDeriv ℝ k.val F x (fun j => cartanCoordinateBasis K n (w j))

private theorem cartanCoordinateFunctional_sum_complex (v : ArchimedeanMatrix K n)
    (L : ArchimedeanMatrix K n →L[ℝ] ℂ) :
    ∑ j : Fin (cartanCoordinateDimension K n),
      (cartanCoordinateFunctional K n j v : ℂ) * L (cartanCoordinateBasis K n j) = L v := by
  have h := congrArg L ((cartanCoordinateBasis K n).sum_repr v)
  change ∑ j : Fin (cartanCoordinateDimension K n),
    ((cartanCoordinateBasis K n).repr v j : ℂ) * L (cartanCoordinateBasis K n j) = L v
  simpa only [map_sum, map_smul, Complex.real_smul, smul_eq_mul] using h

private theorem cartanWord_derivative (k : ℕ)
    (w : Fin k → Fin (cartanCoordinateDimension K n))
    (F : ArchimedeanMatrix K n → ℂ) (x v : ArchimedeanMatrix K n)
    (hF : ContDiffAt ℝ ∞ F x) :
    (∑ j : Fin (cartanCoordinateDimension K n),
      (cartanCoordinateFunctional K n j v : ℂ) *
        iteratedFDeriv ℝ (k + 1) F x
          (Fin.cons (cartanCoordinateBasis K n j) (fun q => cartanCoordinateBasis K n (w q)))) =
      fderiv ℝ (fun y => iteratedFDeriv ℝ k F y
        (fun q => cartanCoordinateBasis K n (w q))) x v := by
  have hd := hF.differentiableAt_iteratedFDeriv (m := k) (by exact_mod_cast ENat.natCast_lt_top k)
  simp_rw [hd.iteratedFDeriv_succ_apply_left']
  simpa only [Fin.cons_zero, Fin.tail_cons] using
    cartanCoordinateFunctional_sum_complex K n v
      (fderiv ℝ (fun y => iteratedFDeriv ℝ k F y
        (fun q => cartanCoordinateBasis K n (w q))) x)

private theorem contDiffAt_cartanArrayAction {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) (x : ArchimedeanMatrix K n)
    (ha : ∀ k w, AnalyticAt ℝ (a k w) x) (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (cartanArrayAction K n a F) x := by
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.sum
  intro w _
  exact (ha k w).contDiffAt.mul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k.val => ArchimedeanMatrix K n) ℂ
      (fun j => cartanCoordinateBasis K n (w j))).contDiff.contDiffAt.comp x
      (hF.iteratedFDeriv_right (by simp)))

private theorem cartanArrayAction_derivative {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) (x v : ArchimedeanMatrix K n)
    (ha : ∀ k w, DifferentiableAt ℝ (a k w) x) (hF : ContDiffAt ℝ ∞ F x) :
    fderiv ℝ (cartanArrayAction K n a F) x v =
      ∑ k : Fin (r + 1), ∑ w : Fin k.val → Fin (cartanCoordinateDimension K n),
        (fderiv ℝ (a k w) x v * iteratedFDeriv ℝ k.val F x
          (fun j => cartanCoordinateBasis K n (w j)) +
        a k w x * fderiv ℝ (fun y => iteratedFDeriv ℝ k.val F y
          (fun j => cartanCoordinateBasis K n (w j))) x v) := by
  have hd (k : Fin (r + 1)) (w : Fin k.val → Fin (cartanCoordinateDimension K n)) :=
    (hF.differentiableAt_iteratedFDeriv (m := k.val) (by exact_mod_cast ENat.natCast_lt_top k.val)).continuousMultilinear_apply_const
      (fun j => cartanCoordinateBasis K n (w j))
  unfold cartanArrayAction
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun k y => ∑ w : Fin k.val → Fin (cartanCoordinateDimension K n),
      a k w y * iteratedFDeriv ℝ k.val F y (fun j => cartanCoordinateBasis K n (w j)))
    (fun k _ => DifferentiableAt.fun_sum (fun w _ => (ha k w).mul (hd k w)))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun w y => a k w y * iteratedFDeriv ℝ k.val F y
      (fun j => cartanCoordinateBasis K n (w j))) (fun w _ => (ha k w).mul (hd k w))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  rw [fderiv_fun_mul (ha k w) (hd k w)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

private theorem cartanArrayAction_left_derivativePart {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n) (x : ArchimedeanMatrix K n) :
    (∑ k : Fin (r + 1 + 1), ∑ w : Fin k.val → Fin (cartanCoordinateDimension K n),
      (if h : k.val ≤ r then fderiv ℝ (a ⟨k.val, Nat.lt_succ_of_le h⟩ w) x (V x) else 0) *
        iteratedFDeriv ℝ k.val F x (fun j => cartanCoordinateBasis K n (w j))) =
    ∑ k : Fin (r + 1), ∑ w : Fin k.val → Fin (cartanCoordinateDimension K n),
      fderiv ℝ (a k w) x (V x) *
        iteratedFDeriv ℝ k.val F x (fun j => cartanCoordinateBasis K n (w j)) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Nat.not_succ_le_self, dite_false, zero_mul,
    Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro w _
  simp only [Fin.val_castSucc, dite_eq_left (Nat.le_of_lt_succ k.isLt)]

private theorem cartanArrayAction_left_prependPart {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n) (x : ArchimedeanMatrix K n)
    (hF : ContDiffAt ℝ ∞ F x) :
    (∑ k : Fin (r + 1 + 1), ∑ w : Fin k.val → Fin (cartanCoordinateDimension K n),
      cartanPrependCoefficient K n a V k.val w x *
        iteratedFDeriv ℝ k.val F x (fun j => cartanCoordinateBasis K n (w j))) =
    ∑ k : Fin (r + 1), ∑ w : Fin k.val → Fin (cartanCoordinateDimension K n),
      a k w x * fderiv ℝ (fun y => iteratedFDeriv ℝ k.val F y
        (fun j => cartanCoordinateBasis K n (w j))) x (V x) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, cartanPrependCoefficient, zero_mul, Finset.sum_const_zero,
    zero_add, Fin.val_succ]
  apply Finset.sum_congr rfl
  intro k _
  simp only [cartanCoefficientExtend, dite_eq_left (Nat.le_of_lt_succ k.isLt)]
  rw [← (Fin.consEquiv (fun _ : Fin (k.val + 1) =>
    Fin (cartanCoordinateDimension K n))).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [← cartanWord_derivative K n k.val w F x (V x) hF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc]
  congr 1

private theorem cartanArrayAction_left {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ)
    (V : ArchimedeanMatrix K n → ArchimedeanMatrix K n) (x : ArchimedeanMatrix K n)
    (ha : ∀ k w, DifferentiableAt ℝ (a k w) x) (hF : ContDiffAt ℝ ∞ F x) :
    cartanArrayAction K n (cartanLeftDirectionalCoefficients K n a V) F x =
      fderiv ℝ (cartanArrayAction K n a F) x (V x) := by
  conv_lhs => unfold cartanArrayAction cartanLeftDirectionalCoefficients
  simp only [add_mul, Finset.sum_add_distrib]
  rw [cartanArrayAction_left_derivativePart, cartanArrayAction_left_prependPart K n a F V x hF]
  rw [cartanArrayAction_derivative K n a F x (V x) ha hF]
  simp only [Finset.sum_add_distrib]

private theorem cartanArrayAction_sum {r : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) (x : ArchimedeanMatrix K n) :
    cartanArrayAction K n (fun k w y => ∑ i, a i k w y) F x =
      ∑ i, cartanArrayAction K n (a i) F x := by
  unfold cartanArrayAction
  simp only [Finset.sum_mul]
  simp_rw [Finset.sum_comm (t := (Finset.univ : Finset ι))]

private theorem cartanDirectional_second (H : ArchimedeanMatrix K n → ℂ)
    (x : ArchimedeanMatrix K n) (hH : ContDiffAt ℝ ∞ H x) (i : CartanBasisIndex K n) :
    fderiv ℝ (fun y => fderiv ℝ H y (cartanMatrixField K n i y)) x (cartanMatrixField K n i x) =
      fderiv ℝ (fderiv ℝ H) x (cartanMatrixField K n i x) (cartanMatrixField K n i x) +
        fderiv ℝ H x (x * (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i) *
          realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))) := by
  have hc := (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hu := (analyticAt_cartanMovingField K n i x).differentiableAt
  rw [fderiv_clm_apply hc hu]
  have hright : fderiv ℝ (cartanMatrixField K n i) x =
      (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip
        (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)) :=
    ((ContinuousLinearMap.mul ℝ (ArchimedeanMatrix K n)).flip
      (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))).fderiv
  simp only [hright, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', cartanMatrixField,
    mul_assoc, add_comm]

private theorem cartanArrayAction_squareSum {r : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) {S : Set (ArchimedeanMatrix K n)}
    (hS : IsOpen S) (ha : ∀ k w, AnalyticOnNhd ℝ (a k w) Set.univ)
    (hF : ContDiffOn ℝ ∞ F S) (x : ArchimedeanMatrix K n) (hx : x ∈ S) :
    cartanArrayAction K n (cartanSquareSumCoefficients K n a) F x =
      cartanAmbientOperator K n (cartanArrayAction K n a F) x := by
  change cartanArrayAction K n (fun k w y => ∑ i : CartanBasisIndex K n,
    cartanLeftDirectionalCoefficients K n
      (cartanLeftDirectionalCoefficients K n a (cartanMatrixField K n i))
      (cartanMatrixField K n i) k w y) F x = _
  rw [cartanArrayAction_sum]
  unfold cartanAmbientOperator
  apply Finset.sum_congr rfl
  intro i _
  have haLeft := analyticOnNhd_cartanLeftDirectionalCoefficients K n (cartanMatrixField K n i)
    (fun y _ => analyticAt_cartanMovingField K n i y) a ha
  rw [cartanArrayAction_left K n _ F _ x
    (fun k w => (haLeft k w x (Set.mem_univ x)).differentiableAt) (hF.contDiffAt (hS.mem_nhds hx))]
  have heq : cartanArrayAction K n (cartanLeftDirectionalCoefficients K n a (cartanMatrixField K n i)) F
      =ᶠ[𝓝 x] fun y => fderiv ℝ (cartanArrayAction K n a F) y (cartanMatrixField K n i y) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact cartanArrayAction_left K n a F _ y
      (fun k w => (ha k w y (Set.mem_univ y)).differentiableAt) (hF.contDiffAt (hS.mem_nhds hy))
  rw [heq.fderiv_eq (𝕜 := ℝ)]
  exact cartanDirectional_second K n _ x
    (contDiffAt_cartanArrayAction K n a F x (fun k w => ha k w x (Set.mem_univ x))
      (hF.contDiffAt (hS.mem_nhds hx))) i

private theorem cartanArrayAction_extend {r s : ℕ}
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) (x : ArchimedeanMatrix K n) (hrs : r ≤ s) :
    cartanArrayAction K n
      (fun (k : Fin (s + 1)) w y => cartanCoefficientExtend K n a k.val w y) F x =
        cartanArrayAction K n a F x := by
  induction s, hrs using Nat.le_induction with
  | base =>
    unfold cartanArrayAction
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro w _
    dsimp only
    rw [cartanCoefficientExtend_of_le K n a w x (Nat.le_of_lt_succ k.isLt)]
  | succ s hrs ih =>
    unfold cartanArrayAction
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last,
      cartanCoefficientExtend_of_lt K n a _ x (by omega : r < s + 1),
      zero_mul, Finset.sum_const_zero, add_zero]
    exact ih

private theorem cartanAmbientOperator_congr_of_eventuallyEq
    (F G : ArchimedeanMatrix K n → ℂ) (x : ArchimedeanMatrix K n)
    (hFG : F =ᶠ[𝓝 x] G) :
    cartanAmbientOperator K n F x = cartanAmbientOperator K n G x := by
  simp only [cartanAmbientOperator, hFG.fderiv_eq (𝕜 := ℝ),
    (hFG.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

private theorem cartanArrayAction_iterate (m : ℕ)
    (F : ArchimedeanMatrix K n → ℂ) {S : Set (ArchimedeanMatrix K n)}
    (hS : IsOpen S) (hF : ContDiffOn ℝ ∞ F S) :
    ∀ x ∈ S, cartanArrayAction K n (cartanIterateCoefficients K n m) F x =
      ((cartanAmbientOperator K n)^[m] F) x := by
  induction m with
  | zero =>
    intro x _
    simp [cartanArrayAction, cartanIterateCoefficients, cartanIdentityCoefficients,
      iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    change cartanArrayAction K n
      (fun (k : Fin (2 * (m + 1) + 1)) w y => cartanCoefficientExtend K n
        (cartanSquareSumCoefficients K n (cartanIterateCoefficients K n m)) k.val w y) F x = _
    rw [cartanArrayAction_extend K n _ F x (by omega)]
    rw [cartanArrayAction_squareSum K n _ F hS (cartanIterateCoefficients_analytic K n m) hF x hx]
    apply cartanAmbientOperator_congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hx] with y hy
    exact ih y hy

private theorem cartanArrayAction_finset_sum {r : ℕ} {ι : Type*}
    (t : Finset ι) (a : ι → CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) (x : ArchimedeanMatrix K n) :
    cartanArrayAction K n (fun k w y => ∑ i ∈ t, a i k w y) F x =
      ∑ i ∈ t, cartanArrayAction K n (a i) F x := by
  unfold cartanArrayAction
  simp only [Finset.sum_mul]
  simp_rw [Finset.sum_comm (t := t)]

private theorem cartanArrayAction_mul {r : ℕ} (c : ℂ)
    (a : CartanCoordinateCoefficients K n r)
    (F : ArchimedeanMatrix K n → ℂ) (x : ArchimedeanMatrix K n) :
    cartanArrayAction K n (fun k w y => c * a k w y) F x =
      c * cartanArrayAction K n a F x := by
  simp only [cartanArrayAction, mul_assoc, Finset.mul_sum]

/-- The actual coefficient operator realizes every Cartan polynomial on any open smooth domain. -/
theorem cartanPolynomialCoordinateOperator_action (p : Polynomial ℂ)
    (F : ArchimedeanMatrix K n → ℂ) {S : Set (ArchimedeanMatrix K n)}
    (hS : IsOpen S) (hF : ContDiffOn ℝ ∞ F S) (x : ArchimedeanMatrix K n) (hx : x ∈ S) :
    (cartanPolynomialCoordinateOperator K n p).action F x =
      cartanAmbientPolynomial K n p F x := by
  change cartanArrayAction K n
    (fun k w y => p.sum fun m c =>
      c * cartanCoefficientExtend K n (cartanIterateCoefficients K n m) k.val w y) F x = _
  unfold Polynomial.sum
  rw [cartanArrayAction_finset_sum]
  simp_rw [cartanArrayAction_mul]
  simp only [cartanAmbientPolynomial, Polynomial.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [cartanArrayAction_extend K n _ F x
    (Nat.mul_le_mul_left 2 (Polynomial.le_natDegree_of_mem_supp m hm))]
  rw [cartanArrayAction_iterate K n m F hS hF x hx]

end Langlands.Global.ArchimedeanGL
