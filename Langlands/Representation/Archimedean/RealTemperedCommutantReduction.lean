import Langlands.Representation.Archimedean.GKModuleOrthogonal
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealTemperedIrreducibleStatement

/-!
# A form and commutant reduction for real tempered standard modules

An anisotropic sesquilinear form, compact invariance and infinitesimal adjoints
up to scalar give invariant complements in the actual function model.
Together with a scalar simultaneous commutant and nontriviality this implies
the unchanged real tempered irreducibility statement.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTemperedCommutantReduction

/-- The actual `O(n)`-finite function space of the real standard module. -/
abbrev KF (n : ℕ) (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-- Sufficient form data on the actual module, including its nontriviality.
The form is linear in the first argument, conjugate-linear in the second.
The last identity allows the real determinant twist through a scalar term. -/
def HasTemperedForm (n : ℕ) (ds : List RealBlock) : Prop :=
  Nontrivial (KF n ds) ∧
    ∃ B : KF n ds →ₗ[ℂ] KF n ds →ₗ⋆[ℂ] ℂ,
      (∀ v : KF n ds, B v v = 0 → v = 0) ∧
      (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (v w : KF n ds),
        B (realStandardRep n ds k v) (realStandardRep n ds k w) = B v w) ∧
      ∀ X : Matrix (Fin n) (Fin n) ℝ, ∃ c : ℂ, ∀ v w : KF n ds,
        B (realStandardLie n ds (1 ⊗ₜ X) v) w +
          B v (realStandardLie n ds (1 ⊗ₜ X) w) = c * B v w

/-- Every endomorphism commuting with the actual compact and complexified Lie
actions on the real standard module is multiplication by a complex scalar. -/
def HasScalarCommutant (n : ℕ) (ds : List RealBlock) : Prop :=
  GKModuleOrthogonal.EndomorphismsAreScalar (realStandardRep n ds) (realStandardLie n ds)

/-- Evaluation at the identity separates vectors along the compact orbit.
This follows from the real Iwasawa decomposition and the principal-series
transformation law. -/
theorem eq_zero_of_compact_eval (n : ℕ) (ds : List RealBlock) (f : KF n ds)
    (hf : ∀ k : Matrix.unitaryGroup (Fin n) ℝ,
      kFiniteEval (realStandardModule n ds) 1 (realStandardRep n ds k f) = 0) :
    f = 0 := by
  apply Subtype.ext
  apply eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact
    (realStandardModule_le_principalSeries n ds f.2.1)
  intro k hk
  let u : Matrix.unitaryGroup (Fin n) ℝ := ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩
  have hu : Unitary.toUnits u = k := Units.ext rfl
  have h := hf u
  rw [kFiniteEval_apply, realStandardRep_apply_coe] at h
  change (f : Langlands.GeneralLinear n ℝ → ℂ) (1 * Unitary.toUnits u) = 0 at h
  simpa only [one_mul, hu] using h

/-- Orthogonals are stable under the complexified Lie action if the real
directions satisfy the form identity appearing in `HasTemperedForm`. -/
theorem orth_lie_mem (n : ℕ) (ds : List RealBlock)
    (B : KF n ds →ₗ[ℂ] KF n ds →ₗ⋆[ℂ] ℂ)
    (hBL : ∀ X : Matrix (Fin n) (Fin n) ℝ, ∃ c : ℂ, ∀ v w : KF n ds,
      B (realStandardLie n ds (1 ⊗ₜ X) v) w +
        B v (realStandardLie n ds (1 ⊗ₜ X) w) = c * B v w)
    (U : Submodule ℂ (KF n ds))
    (hU : ∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ U,
      realStandardLie n ds Z v ∈ U)
    (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) {v : KF n ds}
    (hv : v ∈ ComplexTemperedComplement.orth B U) :
    realStandardLie n ds Z v ∈ ComplexTemperedComplement.orth B U := by
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
      have h1 : realStandardLie n ds (z ⊗ₜ X) =
          z • realStandardLie n ds (1 ⊗ₜ X) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, LinearMap.smul_apply]
      refine Submodule.smul_mem _ z fun w hw => ?_
      obtain ⟨c, hc⟩ := hBL X
      have h := hc v w
      rw [hv w hw, mul_zero, hv _ (hU _ w hw), add_zero] at h
      exact h
  | add Z₁ Z₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ h₁ h₂

/-- Sufficient form data supply simultaneous compact/Lie invariant
complements, by finite vectors and the separating compact orbit functional. -/
theorem hasInvariantComplements_of_form (n : ℕ) (ds : List RealBlock)
    (hform : HasTemperedForm n ds) :
    GKModuleOrthogonal.HasInvariantComplements (realStandardRep n ds) (realStandardLie n ds) := by
  obtain ⟨_, B, hB, hBK, hBL⟩ := hform
  intro U hUK hUL
  refine ⟨ComplexTemperedComplement.orth B U, ComplexTemperedComplement.orth_invariant B hBK U hUK,
    fun Z v hv => orth_lie_mem n ds B hBL U hUL Z hv, ?_⟩
  exact ComplexTemperedComplement.isCompl_orth B hB (kFiniteEval (realStandardModule n ds) 1)
    (eq_zero_of_compact_eval n ds) (isRealGKModule_realStandardModule n ds).1 hBK U hUK

/-- At a fixed list, the form data and scalar commutant imply irreducibility
of the actual real standard module. -/
theorem isIrreducible_of_form_of_scalarCommutant (n : ℕ) (ds : List RealBlock)
    (hform : HasTemperedForm n ds) (hcomm : HasScalarCommutant n ds) :
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) :=
  GKModuleOrthogonal.isIrreducible_of_complements_of_endScalar hform.1
    (hasInvariantComplements_of_form n ds hform) hcomm

end RealTemperedCommutantReduction

/-- Nontriviality and sufficient invariant form data for every rank-correct
list of real blocks whose real exponents are equal. This is an open prerequisite. -/
def RealTemperedFormStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
      RealTemperedCommutantReduction.HasTemperedForm n ds

/-- The scalar simultaneous compact/Lie commutant for every rank-correct
list of real blocks whose real exponents are equal. This is an open prerequisite. -/
def RealTemperedScalarCommutantStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
      RealTemperedCommutantReduction.HasScalarCommutant n ds

/-- Conditional reduction to the unchanged target. Both analytic premises
remain explicit; this theorem does not discharge either of them. -/
theorem realTemperedStandardIrreducible_of_form_of_scalarCommutant
    (hform : RealTemperedFormStatement) (hcomm : RealTemperedScalarCommutantStatement) :
    RealTemperedStandardIrreducibleStatement := by
  intro n ds hr he
  exact RealTemperedCommutantReduction.isIrreducible_of_form_of_scalarCommutant n ds
    (hform n ds hr he) (hcomm n ds hr he)

end Langlands.Archimedean
