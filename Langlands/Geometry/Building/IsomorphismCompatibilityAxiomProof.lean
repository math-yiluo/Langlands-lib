import Langlands.Geometry.Building.IsomorphismCompatibilityAxiomStatement
import Langlands.Geometry.Building.IsomorphismCompatibilityFieldExtension
import Langlands.Geometry.Building.CoveringPointsRingEquiv
import Langlands.Geometry.Building.LocalFieldOrderRingEquiv
import Langlands.Geometry.Building.NormalizerPointsRingEquiv
import Langlands.GroupScheme.Rational.MaximalSplitTorusFieldIso

/-! # Proof of Axiom 4.1.17 for all supplied valuation data -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- **KP Axiom 4.1.17** for arbitrary supplied valuation data: a valued-field isomorphism
`σ : F₁ ≃+* F₂` and a group isomorphism `f_G : G₁ ×_{F₁,σ} F₂ ≅ G₂` induce an equivariant
isomorphism of the reduced buildings of any `B₁`, `B₂` along `coveringPointsMap σ f_G`. -/
theorem isomorphismCompatibilityAxiom : IsomorphismCompatibilityAxiomStatement.{u} := by
  intro F₁ F₂ _ _ _ _ _ _ _ _ σ hσ G₁ _ G₂ _ fG B₁ B₂
  let : Algebra F₁ F₂ := σ.toRingHom.toAlgebra
  have : Mono B₁.i.hom.hom.left := mono_of_isMaximalSplitTorus B₁.isMaximalSplitTorus
  have hmax : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F₁ F₂)).obj B₁.S)
      ((GroupScheme.baseChange (algebraBaseMap F₁ F₂)).map B₁.i) :=
    B₁.isMaximalSplitTorus.baseChange_fieldIso σ
  obtain ⟨Φ, hΦ⟩ := ValuationBuildingData.exists_isEquivariantBuildingIso_of_fieldExtension
    fG B₁ B₂ (localFieldOrder_ringEquiv σ hσ)
    (rationalExtend_bijective_of_bijective F₁ F₂ G₁ σ.bijective)
    (mem_normalizerPoints_rationalExtend_iff B₁.i) hmax
  refine ⟨Φ, ?_⟩
  rw [coveringPointsMap_eq_rationalExtend σ fG.hom]
  exact hΦ

end Langlands.Geometry.Building
