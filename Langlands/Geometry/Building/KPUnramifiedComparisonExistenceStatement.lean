import Langlands.Geometry.Building.KPUnramifiedMoyPrasadComparison

/-!
# Existence of a comparison of building data over `F` and `K = F^ur` (KP §9.6, §9.8)

For building data `P` of `G` over a nonarchimedean local field `F` satisfying the apartment
axioms, there are building data `B` of `G_K` over `K = F^ur` whose centralizer is a torus
and a map `e` of apartments such that `(B, hZ, e)` is a comparison of `P` in the sense of
`ParahoricBuildingData.IsUnramifiedComparison` (KP Construction 9.6.1, Lemma 9.6.3,
Theorem 9.6.5, §9.8.2 and Proposition 9.8.3). This module only states this; it does not
prove it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedComparisonExistenceAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-- Existence of a comparison with `K = F^ur` (KP Construction 9.6.1, Lemma 9.6.3,
Theorem 9.6.5, §9.8.2, Proposition 9.8.3): for building data `P` over `F` satisfying the
apartment axioms there are building data `B` of `G_K` over `K = UnramifiedClosure F` with
torus centralizer and a map `e : P.Apartment → B.Apartment` such that
`P.IsUnramifiedComparison B hZ e`. The body is the hypothesis `hC` of
`unramifiedRationalMoyPrasad_of_unramifiedComparison`. -/
def UnramifiedComparisonExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
      ∃ (B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
        (hZ : IsTorus B.centralizer.Z) (e : P.Apartment → B.Apartment),
        P.IsUnramifiedComparison B hZ e

end Langlands.Geometry.Building
