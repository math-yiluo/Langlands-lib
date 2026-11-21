import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.GroupScheme.Quaternionic.ScalarQuadratic
import Langlands.GroupScheme.Quaternionic.IsometryCut
import Langlands.LinearAlgebra.NumberFieldQuadraticRepresentation

/-! # Local-to-global representation by the norm of pure quaternions -/

noncomputable section

universe u

open Algebra TensorProduct
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

section ConjugateProduct

variable {F A : Type u} [Field F] [Ring A] [Algebra F A]
  (τ : FirstKindInvolution F A) (ℓ : A →ₗ[F] F)

private def conjugateProductForm : QuadraticForm F A :=
  LinearMap.BilinMap.toQuadraticMap
    (((LinearMap.mul F A).compl₁₂ LinearMap.id τ.toLinearMap).compr₂ ℓ)

private theorem conjugateProductForm_apply (x : A) :
    conjugateProductForm τ ℓ x = ℓ (x * τ x) := rfl

/-- The quadratic form of the conjugate product restricted to the alternating subspace. -/
def alternatingNormForm : QuadraticForm F τ.alternatingSubspace :=
  (conjugateProductForm τ ℓ).comp τ.alternatingSubspace.subtype

private theorem alternatingNormForm_apply (x : τ.alternatingSubspace) :
    τ.alternatingNormForm ℓ x = ℓ ((x : A) * τ x) := rfl

private theorem alternatingNormForm_baseChange [Invertible (2 : F)] {R : Type u} [Field R] [Algebra F R] :
    (τ.alternatingNormForm ℓ).baseChange R =
      (conjugateProductForm (τ.baseChange R) (baseChangeScalarFunctional ℓ R)).comp
        (τ.alternatingSubspace.subtype.baseChange R) := by
  apply baseChange_ext
  intro x
  simp only [QuadraticForm.baseChange_tmul, alternatingNormForm_apply,
    QuadraticMap.comp_apply, LinearMap.baseChange_tmul, Submodule.subtype_apply,
    conjugateProductForm_apply, FirstKindInvolution.baseChange_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, baseChangeScalarFunctional_tmul]

end ConjugateProduct

section NumberField

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (τ : FirstKindInvolution F D)
  (hτ : ∀ x : D, x * τ x = algebraMap F D (reducedNorm F D F (1 ⊗ₜ[F] x)))

include hτ in
private theorem exists_alternating_reducedNorm_of_local (a : F)
    (hloc : ∀ v : Global.Place F, let R := Global.placeCompletion F v
      ∃ x : R ⊗[F] D, x ∈ (τ.baseChange R).alternatingSubspace ∧
        reducedNorm F D R x = algebraMap F R a) :
    ∃ x : D, x ∈ τ.alternatingSubspace ∧ reducedNorm F D F (1 ⊗ₜ[F] x) = a := by
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  obtain ⟨ℓ, hℓ⟩ := (Algebra.linearMap F D).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F D).injective)
  have hscalar (s : F) : ℓ (algebraMap F D s) = s := LinearMap.congr_fun hℓ s
  have h1 : ℓ (1 : D) = 1 := by simpa only [_root_.map_one] using hscalar 1
  have hρ (x : τ.alternatingSubspace) : τ.alternatingNormForm ℓ x =
      reducedNorm F D F (1 ⊗ₜ[F] (x : D)) := by
    rw [alternatingNormForm_apply, hτ, hscalar]
  let Q := τ.alternatingNormForm ℓ
  have hzero (x : τ.alternatingSubspace) (hx : Q x = 0) : x = 0 := by
    have hp := hτ (x : D)
    rw [← hρ x, show τ.alternatingNormForm ℓ x = 0 from hx, _root_.map_zero] at hp
    apply Subtype.ext
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · exact τ.injective (h.trans τ.map_zero.symm)
  have hnd : Q.polarBilin.Nondegenerate := by
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply hzero x
    have h := hx x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, ← two_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (two_ne_zero : (2 : F) ≠ 0)
  have localRep {R : Type u} [Field R] [Algebra F R]
      {x : R ⊗[F] D} (hx : x ∈ (τ.baseChange R).alternatingSubspace)
      (ha : reducedNorm F D R x = algebraMap F R a) :
      ∃ y, Q.baseChange R y = algebraMap F R a := by
    have hx' : x ∈ τ.alternatingSubspace.baseChange R := by
      rw [IsometryCut.alternatingSubspace_baseChange]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, ?_⟩
    change (τ.alternatingNormForm ℓ).baseChange R y = _
    rw [alternatingNormForm_baseChange, QuadraticMap.comp_apply, hy, conjugateProductForm_apply,
      τ.conjugation_norm_baseChange hτ R x, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self_apply, baseChangeScalarFunctional_tmul, h1, one_smul, ha]
  have hQloc (v : Global.Place F) : ∃ y, Q.baseChange (Global.placeCompletion F v) y =
      algebraMap F (Global.placeCompletion F v) a := by
    rcases v with v | v
    · obtain ⟨x, hx, ha⟩ := hloc (.inl v)
      exact localRep (R := v.Completion) hx ha
    · obtain ⟨x, hx, ha⟩ := hloc (.inr v)
      exact localRep (R := Global.FiniteCompletion F v) hx ha
  obtain ⟨x, hx⟩ := Langlands.numberFieldQuadraticRepresentation F τ.alternatingSubspace Q a hnd hQloc
  exact ⟨x, x.property, (hρ x).symm.trans hx⟩

end NumberField

/-- Reduced norms of pure quaternions over number fields satisfy the local-to-global
  representation principle used in the quaternionic skew-hermitian isotropy argument. -/
def NumberFieldPureQuaternionNormStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3) (a : F),
    let τ := σ.quaternionConjugation hdim hsym
    (∀ v : Global.Place F, let R := Global.placeCompletion F v
      ∃ x : R ⊗[F] D, x ∈ (τ.baseChange R).alternatingSubspace ∧
        reducedNorm F D R x = algebraMap F R a) →
    ∃ x : D, x ∈ τ.alternatingSubspace ∧ reducedNorm F D F (1 ⊗ₜ[F] x) = a

/-- Apply the number-field quadratic representation theorem to the actual conjugate-product norm. -/
theorem numberFieldPureQuaternionNorm : NumberFieldPureQuaternionNormStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym a τ hloc
  exact exists_alternating_reducedNorm_of_local τ (σ.quaternionConjugation_norm hdim hsym) a hloc

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
