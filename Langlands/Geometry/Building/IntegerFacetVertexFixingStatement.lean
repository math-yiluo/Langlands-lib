import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.NormalizerAffineRootAction

/-! # Fixing closed facets through their original vertices -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- In the original reduced quotient, an element fixing the images of every
vertex of a closed apartment facet fixes the image of its entire closure. -/
def ClosedFacetsFixedByVertices : Prop :=
  ∀ (p : B.Apartment) (h : rationalPoints G),
    (∀ q : B.Apartment,
      q ∈ AffineRootSystem.facetClosure B.affineRoots p →
      AffineRootSystem.IsVertex B.affineRoots q →
      h • B.apartmentMap q = B.apartmentMap q) →
    ∀ x ∈ AffineRootSystem.facetClosure B.affineRoots p,
      h • B.apartmentMap x = B.apartmentMap x

end IntegerValuationBuildingData

/-- A model-free closed-facet fixation prerequisite over any integer-valued
field. The corrected affine root system and affine Weyl lifting are supplied;
no topology, local-field structure or integral model on the field is assumed. -/
def IntegerFacetVertexFixingStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G),
    AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots →
    AffineRootSystem.affineWeylGroup B.affineRoots ≤
      B.apartment.normalizerAffineEquiv.range →
    B.ClosedFacetsFixedByVertices

end Langlands.Geometry.Building
