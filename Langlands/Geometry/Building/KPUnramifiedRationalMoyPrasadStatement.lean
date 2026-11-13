import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.KPRationalMoyPrasadFamily
import Langlands.GroupScheme.GaloisPointRational

/-!
# The rational Moy–Prasad family from the maximal unramified extension

The F-to-K existence input for KP §9.8: after choosing building data over the actual
maximal unramified extension and a map of apartments, the inverse images of the
published groups `G(K)_{x,r}` form a rational Moy–Prasad family over `F`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedRationalMoyPrasadAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-- The F-to-K link of KP §9.8 (Lemma 9.8.1 and Proposition 9.8.3): there are building
data `B` over `K = F^ur` with torus centralizer and an apartment map `e` such that
`Q y r = G(K)_{e y,r} ∩ G(F)` has the ten properties of a rational Moy–Prasad family.
The upstairs groups are exactly `MaximalUnramified.BuildingData.moyPrasad`. -/
def UnramifiedRationalMoyPrasadStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
      ∃ (B : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
        (hZ : IsTorus B.centralizer.Z) (e : P.Apartment → B.Apartment),
        P.IsRationalMoyPrasadFamily
          (fun y r => (B.moyPrasad hZ (e y) r).comap
            (rationalExtend F (UnramifiedClosure F) G))

end Langlands.Geometry.Building
