import Langlands.Geometry.Building.ValuationAffineRootSystems
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.Geometry.Building.AffineWeylFacetFixing
import Langlands.Geometry.Building.ValuationBuildingQuotientMap
import Langlands.Geometry.Building.AffineFacetVertexIncidence

/-! # Rational-point translates of one closed chamber cover the reduced building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.ValuationBuildingData

open AffineRootSystem AffineRootSystem.GalleryGeometry

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The map from rational points and the closure of the facet of `c` to the reduced building. -/
def closedChamberOrbitMap (c : B.Apartment) :
    rationalPoints G × facetClosure B.affineRoots c → B.ReducedBuilding :=
  fun gx => gx.1 • B.apartmentMap gx.2.val

/-- For regular `c`, every apartment point is an actual normalizer translate of a point of
`facetClosure B.affineRoots c`. -/
theorem exists_normalizer_smul_of_mem_closedChamber {c : B.Apartment}
    (hc : IsRegular B.affineRoots c) (x : B.Apartment) :
    ∃ n : normalizerPoints B.i, ∃ y ∈ facetClosure B.affineRoots c, n • y = x := by
  have hΨ := B.isAffineRootSystemWithRankZero_affineRoots
  obtain ⟨d, hd, hx⟩ := hΨ.isLocallyFiniteReflectionArrangement.exists_regularPoint_closure x
  obtain ⟨w, hw, -⟩ := affineChamberSimpleTransitivity _ _ _ hΨ _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  obtain ⟨n, hn⟩ := B.affineWeylGroup_le_range_of_AS3 hΨ w.property
  let e := B.apartment.normalizerAffineEquiv n
  have hroot : e ∈ rootStabilizer B.affineRoots :=
    B.apartment.normalizerAffineEquiv_mem_rootStabilizer n
  have hroot' := transportedRoots_eq_of_mem_rootStabilizer_algebraic hroot
  have hc' : facet B.affineRoots (e c) = facet B.affineRoots d := by
    rw [← image_facet hroot]
    change (B.apartment.normalizerAffineEquiv n : B.Apartment → B.Apartment) '' _ = _
    rw [hn]
    exact hw
  have hclosure : e '' facetClosure B.affineRoots c = facetClosure B.affineRoots d := by
    rw [image_facetClosure_transportedRoots, hroot']
    exact facetClosure_eq_facetClosure_iff.2 (facet_eq_facet_iff.1 hc')
  obtain ⟨y, hy, hxy⟩ := hclosure ▸ hx
  exact ⟨n, y, hy, hxy⟩

/-- Every point of the supplied reduced building lies in a rational-point translate of the
closure of this particular chamber. No choice of a chamber depending on the building point
remains in the statement. -/
theorem closedChamberOrbitMap_surjective {c : B.Apartment} (hc : IsRegular B.affineRoots c) :
    Function.Surjective (B.closedChamberOrbitMap c) := by
  intro z
  obtain ⟨g, x, hx⟩ := B.exists_smul_apartmentMap z
  obtain ⟨n, y, hy, hxy⟩ := B.exists_normalizer_smul_of_mem_closedChamber hc x
  refine ⟨⟨g * (n : rationalPoints G), ⟨y, hy⟩⟩, ?_⟩
  rw [closedChamberOrbitMap, mul_smul, normalizer_smul_apartmentMap, hxy, hx]

end Langlands.Geometry.Building.ValuationBuildingData
