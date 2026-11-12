import Langlands.Geometry.Building.FullValidity.AssignmentReplacement

/-! # Turning inner-equivariance into identity-equivariance -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Translation by an actual rational point preserves the building geometry.
On the chart indexed by h it changes the index to g*h and leaves the affine
apartment coordinate unchanged. -/
theorem isBuildingIso_smul (B : ValuationBuildingData G) (g : rationalPoints G) :
    IsBuildingIso B B (MulAction.toPerm g) where
  isFacet_image_iff Y := by
    constructor
    · intro h
      have h' := h.smul B g⁻¹
      simpa only [MulAction.toPerm_apply, Set.image_image, inv_smul_smul,
        Set.image_id'] using h'
    · exact fun h => h.smul B g
  isApartment_image_iff Y := by
    change B.IsApartment (g • Y) ↔ B.IsApartment Y
    constructor
    · intro h
      simpa only [inv_smul_smul] using h.smul B g⁻¹
    · exact fun h => h.smul B g
  exists_affineEquiv h := ⟨g * h, AffineEquiv.refl ℝ _, fun x => by
    change g • (h • B.apartmentMap x) = (g * h) • B.apartmentMap x
    exact (mul_smul _ _ _).symm⟩

end ValuationBuildingData

namespace KPBuildingDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (D E : KPBuildingDatum G) (g : rationalPoints G)
  (Φ : D.base.ReducedBuilding ≃ E.base.ReducedBuilding)
  (hΦ : ValuationBuildingData.IsEquivariantBuildingIso D.base.toValuationBuildingData
    E.base.toValuationBuildingData (rationalPoints.map (G.innerIso g).hom) Φ)
  (hinv : ValuationBuildingData.IsBuildingIso E.base.toValuationBuildingData
    D.base.toValuationBuildingData Φ.symm)

/-- Correct an inner-equivariant building comparison by translation on its
source. The result intertwines the identity on the actual rational-point group. -/
def BuildingEquivalence.ofInner : BuildingEquivalence D E where
  equiv := (MulAction.toPerm g⁻¹).trans Φ
  isBuildingIso := (ValuationBuildingData.isBuildingIso_smul _ g⁻¹).trans hΦ.1
  isBuildingIso_symm := by
    convert hinv.trans (ValuationBuildingData.isBuildingIso_smul _ g) using 1
    ext y
    simp
  equivariant k y := by
    change Φ (g⁻¹ • (k • y)) = k • Φ (g⁻¹ • y)
    have h := hΦ.2 (g⁻¹ * k * g) (g⁻¹ • y)
    simpa only [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self,
      mul_smul, inv_smul_smul, smul_inv_smul] using h

end KPBuildingDatum
end Langlands.Geometry.Building
