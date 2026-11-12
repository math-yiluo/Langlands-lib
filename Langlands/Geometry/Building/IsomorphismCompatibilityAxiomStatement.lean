import Langlands.Geometry.Building.FullValidity.Assignment

/-! # Axiom 4.1.17 for all supplied valuation data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- KP Axiom 4.1.17 (compatibility with isomorphisms) for arbitrary supplied valuation data on
both sides: for nonarchimedean local fields `F₁`, `F₂`, an isomorphism of valued fields
`σ : F₁ → F₂`, groups `G₁` over `F₁` and `G₂` over `F₂`, an isomorphism
`f_G : G₁ ×_{F₁,σ} F₂ → G₂`, and any data `B₁`, `B₂` for `G₁`, `G₂`, there is an isomorphism of
buildings `f_B : B(G₁) → B(G₂)` with `f_B(g · y) = f_G(g) · f_B(y)`.

Here `B(Gᵢ)` is the existing quotient of the supplied `ValuationBuildingData`. This is the
clause `HasIsomorphismCompatibility` of `KPBuildingAssignment`, asserted for every choice of
data. No existence of data is asserted. -/
def IsomorphismCompatibilityAxiomStatement : Prop :=
  ∀ (F₁ F₂ : Type u) [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁]
    [IsNonarchimedeanLocalField F₁] [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂]
    [IsNonarchimedeanLocalField F₂] (σ : F₁ ≃+* F₂), IsValuativeRingEquiv σ →
    ∀ (G₁ : GroupScheme (Spec (CommRingCat.of F₁))) [IsAffineHom G₁.X.hom]
      (G₂ : GroupScheme (Spec (CommRingCat.of F₂))) [IsAffineHom G₂.X.hom]
      (fG : (GroupScheme.baseChange (specMapOfRingEquiv σ)).obj G₁ ≅ G₂)
      (B₁ : ValuationBuildingData G₁) (B₂ : ValuationBuildingData G₂),
      ∃ Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding,
        ValuationBuildingData.IsEquivariantBuildingIso B₁ B₂ (coveringPointsMap σ fG.hom) Φ

end Langlands.Geometry.Building
