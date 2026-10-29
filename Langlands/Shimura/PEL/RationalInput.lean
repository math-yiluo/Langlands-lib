import Langlands.Shimura.PEL.ScalarExtension
import Langlands.Shimura.PEL.TraceSimilitudesBaseChange

/-! # Rational PEL source hypotheses and scalar-extended forms -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Algebra

/-- A nondegenerate field-valued form on a nonzero module takes the value one. -/
theorem bilinForm_attains_one {F M : Type*} [Field F] [AddCommGroup M]
    [Module F M] [Nontrivial M] (ψ : LinearMap.BilinForm F M)
    (hψ : ψ.Nondegenerate) : ∃ x y, ψ x y = 1 := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hy : ∃ y, ψ x y ≠ 0 := by
    by_contra! hz
    exact hx (hψ.1 x hz)
  obtain ⟨y, hxy⟩ := hy
  refine ⟨(ψ x y)⁻¹ • x, y, ?_⟩
  simp [map_smul, LinearMap.smul_apply, smul_eq_mul, hxy]

/-- A value-one pair remains a value-one pair after arbitrary scalar extension. -/
theorem bilinForm_baseChange_attains_one {F M R : Type*} [Field F]
    [AddCommGroup M] [Module F M] [CommRing R] [Algebra F R]
    (ψ : LinearMap.BilinForm F M) (hψ : ∃ x y, ψ x y = 1) :
    ∃ x y, ψ.baseChange R x y = 1 := by
  obtain ⟨x, y, hxy⟩ := hψ
  exact ⟨(1 : R) ⊗ₜ[F] x, (1 : R) ⊗ₜ[F] y, by simp [hxy]⟩

/-- Alternation of a rational form survives arbitrary commutative scalar extension. -/
theorem bilinForm_baseChange_isAlt {M R : Type*} [AddCommGroup M]
    [Module ℚ M] [CommRing R] [Algebra ℚ R]
    (ψ : LinearMap.BilinForm ℚ M) (hψ : ψ.IsAlt) : (ψ.baseChange R).IsAlt := by
  have hskew (x y : R ⊗[ℚ] M) :
      ψ.baseChange R y x = -ψ.baseChange R x y := by
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx', neg_add]
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' =>
        simp only [map_add, LinearMap.add_apply, hy, hy', neg_add]
      | tmul b y =>
        simp only [LinearMap.BilinForm.baseChange_tmul, ← hψ.neg_eq x y,
          neg_smul, mul_comm b a]
  intro x
  have h2 : (2 : ℚ) • ψ.baseChange R x x = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (hskew x x)
  have hh := congrArg (fun r : R => (1 / 2 : ℚ) • r) h2
  simpa only [smul_smul, show (1 / 2 : ℚ) * 2 = 1 by norm_num,
    one_smul, smul_zero] using hh

end Langlands.Algebra

namespace Langlands.Shimura.PEL

variable {D V : Type*} [Ring D] [Algebra ℚ D]
  [AddCommGroup V] [Module ℚ V] [Module D V]
  (σ : AlgebraInvolution ℚ D) (ψ : LinearMap.BilinForm ℚ V)

/-- The finite, faithful algebraic source conditions needed for PEL levels.
Nonzeroness, positivity, Hodge and integral conditions are separate. -/
def RationalPELConditions : Prop :=
  IsScalarTower ℚ D V ∧ FiniteDimensional ℚ D ∧ FiniteDimensional ℚ V ∧
    FaithfulSMul D V ∧ ψ.IsAlt ∧ ψ.Nondegenerate ∧ FormRespectsInvolution σ ψ

namespace RationalPELConditions

variable {σ ψ} (h : RationalPELConditions σ ψ)

include h

theorem scalarTower : IsScalarTower ℚ D V := h.1

theorem finite_algebra : FiniteDimensional ℚ D := h.2.1

theorem finite_module : FiniteDimensional ℚ V := h.2.2.1

theorem faithful : FaithfulSMul D V := h.2.2.2.1

theorem isAlt : ψ.IsAlt := h.2.2.2.2.1

theorem nondegenerate : ψ.Nondegenerate := h.2.2.2.2.2.1

theorem respectsInvolution : FormRespectsInvolution σ ψ := h.2.2.2.2.2.2

variable (R : Type*) [CommRing R] [Algebra ℚ R]

theorem baseChange_isAlt : (ψ.baseChange R).IsAlt :=
  Langlands.Algebra.bilinForm_baseChange_isAlt ψ h.isAlt

/-- Reuse the existing finite-dimensional arbitrary-ring nondegeneracy theorem. -/
theorem baseChange_nondegenerate : (ψ.baseChange R).Nondegenerate := by
  let : FiniteDimensional ℚ V := h.finite_module
  exact Langlands.Algebra.bilinForm_baseChange_nondegenerate ψ h.nondegenerate

/-- Nonzero source is explicit: the zero-module boundary does not determine multipliers. -/
theorem baseChange_attains_one [Nontrivial V] :
    ∃ x y, ψ.baseChange R x y = 1 :=
  Langlands.Algebra.bilinForm_baseChange_attains_one ψ
    (Langlands.Algebra.bilinForm_attains_one ψ h.nondegenerate)

/-- In the scalar-extended PEL source, the underlying operator determines the multiplier. -/
theorem scalarExtension_underlying_injective [Nontrivial V] :
    letI := h.scalarTower
    letI := scalarExtensionAlgebraModule D V R
    Function.Injective
      (bilinearSimilitudes.underlying (B := D ⊗[ℚ] R) (ψ.baseChange R)) := by
  let := h.scalarTower
  let := scalarExtensionAlgebraModule D V R
  exact bilinearSimilitudes.underlying_injective (ψ.baseChange R)
    (h.baseChange_attains_one R)

end RationalPELConditions
end Langlands.Shimura.PEL
