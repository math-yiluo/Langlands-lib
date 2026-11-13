import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement
import Langlands.Geometry.Building.KPZeroSubgroups

/-! # Apartment-compatible descent of the building from the maximal unramified extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- **Apartment-compatible unramified descent of the building** (Kaletha–Prasad
§9.2, Theorem 9.2.7, Propositions 9.3.13 and 9.9.2). Every existing building
quotient `B` of a connected reductive group over a nonarchimedean local field
`F` embeds injectively and `G(F)`-equivariantly into a building quotient `C`
over the maximal unramified extension `K` with a semilinear `Aut(K/F)`-action.
The embedding sends the apartment of `B` into the apartment of `C` through a
real affine map of apartments, its image consists of Galois-fixed points and
contains every Galois-fixed point, and a point whose image is special upstairs
is special downstairs. The facets of the apartment of `B` for its affine roots are
exactly the preimages under the apartment map of the facets of the apartment of `C`
(Proposition 9.4.28 and Corollary 9.4.31). Finally, the maximal bounded subgroup `S(K)^1` of
the group `S(K)` of the split torus `S_K` fixes the image of the apartment of `B` pointwise (§9.2.2–9.2.3,
Proposition 9.3.16): that image lies in the apartment of `T_K` for a special torus `T ⊇ S`. -/
def UnramifiedApartmentDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ B : ValuationBuildingData G,
      ∃ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
        (D : MaximalUnramified.SemilinearApartmentData C)
        (e : B.ReducedBuilding → C.ReducedBuilding)
        (a : B.Apartment →ᵃ[ℝ] C.Apartment),
        Function.Injective e ∧
        (∀ (g : rationalPoints G) (z : B.ReducedBuilding),
          e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z) ∧
        (∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w)) ∧
        (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) (z : B.ReducedBuilding),
          D.action σ (e z) = e z) ∧
        (∀ y : C.ReducedBuilding,
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ y = y) →
            ∃ z : B.ReducedBuilding, e z = y) ∧
        (∀ z : B.ReducedBuilding, C.IsSpecialPoint (e z) → B.IsSpecialPoint z) ∧
        (∀ w : B.Apartment,
          a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
            AffineRootSystem.facet B.affineRoots w) ∧
        ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
            (baseChanged F (inertiaFixedField F) B.S.toGrp),
          ∀ w : B.Apartment,
            rationalPoints.map
                ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i) s •
              e (B.apartmentMap w) = e (B.apartmentMap w)

/-- The apartment-compatible statement strengthens the published
`UnramifiedBuildingDescentStatement`: forgetting the apartment map, the
fixedness of the image, the facet clause and the torus clause gives its four conclusions. -/
theorem unramifiedBuildingDescentStatement_of_apartmentDescent
    (h : UnramifiedApartmentDescentStatement.{u}) :
    UnramifiedBuildingDescentStatement.{u} := by
  intro F _ _ _ _ G hG B
  obtain ⟨C, D, e, _a, hinj, hsmul, _hapt, _hfix, hsurj, hspec, _hfacet, _htorus⟩ :=
    h F G hG B
  exact ⟨C, D, e, hinj, hsmul, hsurj, hspec⟩

end Langlands.Geometry.Building
