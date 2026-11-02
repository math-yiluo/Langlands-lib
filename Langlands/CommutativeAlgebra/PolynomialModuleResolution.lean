import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The canonical polynomial-action exact sequence -/

universe u v

namespace Langlands.CommutativeAlgebra

open Polynomial PolynomialModule
open CategoryTheory

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module R[X] M] [IsScalarTower R R[X] M]

/-- Coefficientwise action of `X` on the induced polynomial module. -/
noncomputable def polynomialCoefficientAction :
    PolynomialModule R M →ₗ[R[X]] PolynomialModule R M where
  __ := PolynomialModule.map R (DistribSMul.toLinearMap R M (X : R[X]))
  map_smul' p q := by
    simpa using PolynomialModule.map_smul R
      (DistribSMul.toLinearMap R M (X : R[X])) p q

/-- The map sending `p(X) ⊗ m` to `p(X) • m` for the specified action on `M`. -/
noncomputable def polynomialActionEvaluation : PolynomialModule R M →ₗ[R[X]] M :=
  (LinearMap.id (R := R) (M := M)).liftBaseChange R[X] ∘ₗ
    (polynomialTensorProductLEquivPolynomialModule R M).symm.toLinearMap

omit [Module R[X] M] [IsScalarTower R R[X] M] in
private theorem polynomialTensor_single (n : ℕ) (m : M) :
    polynomialTensorProductLEquivPolynomialModule R M (((X : R[X]) ^ n) ⊗ₜ[R] m) =
      single R n m := by
  simp [polynomialTensorProductLEquivPolynomialModule,
    ← Polynomial.monomial_one_right_eq_X_pow]
  rfl

@[simp]
theorem polynomialActionEvaluation_single (n : ℕ) (m : M) :
    polynomialActionEvaluation (single R n m) = (X : R[X]) ^ n • m := by
  rw [← polynomialTensor_single n m]
  simp [polynomialActionEvaluation]

@[simp]
theorem polynomialCoefficientAction_single (n : ℕ) (m : M) :
    polynomialCoefficientAction (single R n m) = single R n ((X : R[X]) • m) := by
  exact PolynomialModule.map_single ..

/-- The difference between multiplying the polynomial variable and acting by `X`
coefficientwise. -/
noncomputable def polynomialActionDifference :
    PolynomialModule R M →ₗ[R[X]] PolynomialModule R M :=
  LinearMap.lsmul R[X] (PolynomialModule R M) X - polynomialCoefficientAction

@[simp]
theorem polynomialActionDifference_single (n : ℕ) (m : M) :
    polynomialActionDifference (single R n m) =
      single R (n + 1) m - single R n ((X : R[X]) • m) := by
  have hX : (X : R[X]) = monomial 1 1 := rfl
  simp [polynomialActionDifference, hX, Nat.add_comm]

theorem polynomialActionEvaluation_difference (p : PolynomialModule R M) :
    polynomialActionEvaluation (polynomialActionDifference p) = 0 := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single n m => simp [pow_succ, mul_smul]

theorem polynomialActionDifference_coeff_succ (p : PolynomialModule R M) (n : ℕ) :
    (polynomialActionDifference p).coeff (n + 1) =
      p.coeff n - (X : R[X]) • p.coeff (n + 1) := by
  change ((X : R[X]) • p).coeff (n + 1) - (X : R[X]) • p.coeff (n + 1) = _
  have hX : (X : R[X]) = monomial 1 1 := rfl
  simp [hX]

/-- The difference map is injective, without finiteness hypotheses on `M`. -/
theorem polynomialActionDifference_injective :
    Function.Injective (polynomialActionDifference (R := R) (M := M)) := by
  classical
  apply (injective_iff_map_eq_zero _).2
  intro p hp
  by_contra hne
  have hs : p.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.2 (by simpa using hne)
  let d := p.coeff.support.max' hs
  have hd : d ∈ p.coeff.support := Finset.max'_mem _ _
  have htop : p.coeff (d + 1) = 0 := by
    apply Finsupp.notMem_support_iff.1
    intro hmem
    have hle : d + 1 ≤ d := Finset.le_max' _ _ hmem
    omega
  have hz := congrArg (fun q : PolynomialModule R M => q.coeff (d + 1)) hp
  rw [polynomialActionDifference_coeff_succ, htop, smul_zero, sub_zero] at hz
  exact Finsupp.mem_support_iff.1 hd hz

private theorem polynomialAction_monomial_remainder (n : ℕ) (m : M) :
    single R n m - single R 0 ((X : R[X]) ^ n • m) ∈
      LinearMap.range (polynomialActionDifference (R := R) (M := M)) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    have hδ : single R (n + 1) m - single R n ((X : R[X]) • m) ∈
        LinearMap.range (polynomialActionDifference (R := R) (M := M)) :=
      ⟨single R n m, polynomialActionDifference_single n m⟩
    simpa only [sub_add_sub_cancel, pow_succ, mul_smul] using
      (LinearMap.range (polynomialActionDifference (R := R) (M := M))).add_mem
        hδ (ih ((X : R[X]) • m))

/-- Subtracting the constant evaluation of a polynomial gives a difference. -/
theorem polynomialActionEvaluation_remainder_mem_range (p : PolynomialModule R M) :
    p - single R 0 (polynomialActionEvaluation p) ∈
      LinearMap.range (polynomialActionDifference (R := R) (M := M)) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add p q hp hq =>
    have h := (LinearMap.range (polynomialActionDifference (R := R) (M := M))).add_mem
      hp hq
    simpa only [map_add, single_add, sub_add_sub_comm] using h
  | single n m =>
    simpa only [polynomialActionEvaluation_single] using
      polynomialAction_monomial_remainder n m

theorem polynomialActionDifference_range_eq_ker :
    LinearMap.range (polynomialActionDifference (R := R) (M := M)) =
      LinearMap.ker polynomialActionEvaluation := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact polynomialActionEvaluation_difference q
  · intro hp
    change polynomialActionEvaluation p = 0 at hp
    simpa [hp] using polynomialActionEvaluation_remainder_mem_range p

theorem polynomialActionEvaluation_surjective :
    Function.Surjective (polynomialActionEvaluation (R := R) (M := M)) := by
  intro m
  exact ⟨single R 0 m, by simp⟩

/-- The actual canonical polynomial-action complex over `R[X]`. -/
noncomputable def polynomialActionShortComplex : ShortComplex (ModuleCat.{v} R[X]) :=
  ShortComplex.moduleCatMk (polynomialActionDifference (R := R) (M := M))
    polynomialActionEvaluation
    (by ext p; exact polynomialActionEvaluation_difference p)

theorem polynomialActionShortComplex_shortExact :
    (polynomialActionShortComplex (R := R) (M := M)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (polynomialActionDifference (R := R) (M := M))
      polynomialActionEvaluation
    exact LinearMap.exact_iff.2
      (polynomialActionDifference_range_eq_ker (R := R) (M := M)).symm
  · change Function.Injective (polynomialActionDifference (R := R) (M := M))
    exact polynomialActionDifference_injective
  · change Function.Surjective (polynomialActionEvaluation (R := R) (M := M))
    exact polynomialActionEvaluation_surjective

end Langlands.CommutativeAlgebra
