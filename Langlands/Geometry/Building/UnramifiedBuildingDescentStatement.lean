import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction

/-! # Descent of the existing building quotient from the maximal unramified extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

private instance unramifiedBuildingDescentAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Every existing building quotient of a connected reductive group over a
nonarchimedean local field embeds equivariantly into a building quotient over
the maximal unramified extension carrying a semilinear Galois action, with image
containing every Galois-fixed point, and a point whose image is special upstairs
is special downstairs (Kaletha–Prasad, §9.2 and Proposition 9.9.2). -/
def UnramifiedBuildingDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ B : ValuationBuildingData G,
      ∃ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
        (D : MaximalUnramified.SemilinearApartmentData C)
        (e : B.ReducedBuilding → C.ReducedBuilding),
        Function.Injective e ∧
        (∀ (g : rationalPoints G) (z : B.ReducedBuilding),
          e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z) ∧
        (∀ y : C.ReducedBuilding,
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ y = y) →
            ∃ z : B.ReducedBuilding, e z = y) ∧
        ∀ z : B.ReducedBuilding, C.IsSpecialPoint (e z) → B.IsSpecialPoint z

end Langlands.Geometry.Building
