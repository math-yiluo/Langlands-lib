import Langlands.Global.FiniteCompletionLocalField
import Langlands.LinearAlgebra.LocalQuadraticAnisotropicDimensionBound
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof

/-! # Local-to-global representation by a quadratic form over a number field -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands

/-- Representation of a scalar by a regular quadratic form is local-to-global. -/
def NumberFieldQuadraticRepresentationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F],
    let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
    ∀ (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (q : QuadraticForm F V) (a : F), q.polarBilin.Nondegenerate →
      (∀ v : Global.Place F, ∃ y,
        (q.baseChange (Global.placeCompletion F v)) y = algebraMap F (Global.placeCompletion F v) a) →
      ∃ y, q y = a

/-- The representation theorem follows from Hasse–Minkowski isotropy. -/
theorem numberFieldQuadraticRepresentation : NumberFieldQuadraticRepresentationStatement.{u} := by
  intro F _ _ _ V _ _ _ q a hq hlocal
  exact QuadraticIsometryReduction.represents_of_local
    (numberFieldQuadraticIsotropy_of_cyclicNorm ClassFieldTheory.Global.cyclicHasseNorm) q hq a hlocal

/-- In dimension at least four, only the archimedean representation conditions are needed. -/
theorem numberFieldQuadraticRepresentation_of_archimedean
    {F V : Type u} [Field F] [NumberField F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (q : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate)
    (hrank : 4 ≤ Module.finrank F V) (a : F) :
    let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
    (∀ v : NumberField.InfinitePlace F, ∃ y,
      (q.baseChange (Global.placeCompletion F (.inl v))) y =
        algebraMap F (Global.placeCompletion F (.inl v)) a) →
    ∃ y, q y = a := by
  intro inst h
  apply QuadraticIsometryReduction.represents_of_local_lineProduct_isotropy
    (numberFieldQuadraticIsotropy_of_cyclicNorm ClassFieldTheory.Global.cyclicHasseNorm) q hq a
  intro v
  rcases v with v | v
  · exact QuadraticIsometryReduction.lineProduct_baseChange_not_anisotropic_of_represents
      q a (.inl v) (h v)
  · let K := Global.FiniteCompletion F v
    let : ValuativeRel K := Global.FiniteCompletion.valuativeRel v
    let : IsNonarchimedeanLocalField K := Global.FiniteCompletion.isNonarchimedeanLocalField v
    intro han
    have hb := localQuadraticAnisotropicDimensionBound K (K ⊗[F] (F × V)) _ han
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_self] at hb
    omega

end Langlands
