import Langlands.Geometry.Building.KPParahoric
import Langlands.Geometry.Building.KPApartmentAxioms

/-!
# `N(F) ∩ G(F)^♮` acts on the apartment through `W_aff` (KP Theorem 7.5.3(2))

Statement, not proof: the image of `N^♮ = N(F) ∩ G(F)^♮` in the affine automorphisms of the
apartment is the affine Weyl group `W(Ψ)` of the affine roots.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

/-- KP Theorem 7.5.3(2) for the Tits system `(G^♮, I^♮, N^♮, R)`, range part: on the actual
building data `P` of a connected reductive group `G` over a nonarchimedean local field `F`,
under the apartment axioms of the corrected KP Chapter 7, the action on the apartment maps
`N^♮ = N(F) ∩ G(F)^♮` onto the affine Weyl group `W(Ψ)` of the affine roots. -/
def SimplyConnectedNormalizerAffineWeylStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
          P.apartment.normalizerAffineEquiv =
        AffineRootSystem.affineWeylGroup P.affineRoots

end Langlands.Geometry.Building
