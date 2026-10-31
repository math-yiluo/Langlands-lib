import Langlands.Algebra.FilteredRetractedSpanning
import Langlands.Global.ArchimedeanCartanFilteredRetraction

/-! # Filtered Cartan symmetrization on compact-stable modules -/

noncomputable section
universe u w
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open Langlands.Algebra.UniversalEnveloping

variable (K : Type u) [Field K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual symmetrizations of Cartan tensors of bounded monomial length. -/
def cartanSymmetrizationSpan (d : ℕ) : Submodule ℂ (EnvelopingAlgebra K n) :=
  (cartanSymmetricDegreeFiltration K n d).map (cartanSymmetricAlgebraSymmetrize K n)

/-- The generic retracted symmetric image is exactly the actual Cartan image. -/
theorem retractedSymmetrizationSpan_cartan (d : ℕ) :
    retractedSymmetrizationSpan ℂ (ComplexLieAlgebra K n)
        ((cartanComplexInclusion K n).comp (cartanComplexProjection K n)) d =
      cartanSymmetrizationSpan K n d := by
  apply le_antisymm
  · rintro a ⟨P, hP, rfl⟩
    refine ⟨cartanSymmetricProjection K n P,
      cartanSymmetricProjection_mem_degreeFiltration K n hP, ?_⟩
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      symmetricLinearLift_cartanProjection, AlgHom.comp_apply,
      cartanSymmetricAlgebraSymmetrize_apply, lieSymmetricAlgebraSymmetrize]
  · rintro a ⟨Q, hQ, rfl⟩
    refine ⟨cartanSymmetricInclusion K n Q,
      cartanSymmetricInclusion_mem_degreeFiltration K n hQ, ?_⟩
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      symmetricLinearLift_cartanProjection, AlgHom.comp_apply,
      cartanSymmetricProjection_inclusion, cartanSymmetricAlgebraSymmetrize_apply,
      lieSymmetricAlgebraSymmetrize]

theorem cartanSymmetrizationSpan_mono : Monotone (cartanSymmetrizationSpan K n) := by
  intro d e h
  rw [← retractedSymmetrizationSpan_cartan, ← retractedSymmetrizationSpan_cartan]
  exact retractedSymmetrizationSpan_mono ℂ (ComplexLieAlgebra K n) _ h

theorem cartanSymmetrizationSpan_le (d : ℕ) :
    cartanSymmetrizationSpan K n d ≤ envelopingDegreeFiltration K n d := by
  rw [← retractedSymmetrizationSpan_cartan]
  exact retractedSymmetrizationSpan_le ℂ (ComplexLieAlgebra K n) _ d

theorem one_mem_cartanSymmetrizationSpan (d : ℕ) :
    (1 : EnvelopingAlgebra K n) ∈ cartanSymmetrizationSpan K n d := by
  rw [← retractedSymmetrizationSpan_cartan]
  exact one_mem_retractedSymmetrizationSpan ℂ (ComplexLieAlgebra K n) _ d

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

/-- On every genuine compact-stable subspace, bounded Cartan symmetrizations
span exactly the full filtered enveloping orbit. -/
theorem cartanSymmetrizationSpan_smul_eq (W : Submodule ℂ V)
    (hW : ∀ X : CompactComplexLieAlgebra K n, ∀ w ∈ W,
      compactEnvelopingGenerator K n X • w ∈ W) (d : ℕ) :
    cartanSymmetrizationSpan K n d • W = envelopingDegreeFiltration K n d • W := by
  rw [← retractedSymmetrizationSpan_cartan]
  apply retractedSymmetrizationSpan_smul_eq ℂ (ComplexLieAlgebra K n)
    (compactComplexDirections K n) _
    (sub_cartanComplexProjection_mem K n) W
  rintro X ⟨Y, rfl⟩ w hw
  exact hW Y w hw

end Module

end Langlands.Global.ArchimedeanGL
