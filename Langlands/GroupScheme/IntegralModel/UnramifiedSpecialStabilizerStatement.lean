import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent

/-! # The special-stabilizer identity after maximal unramified base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

private instance unramifiedSpecialStabilizerAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- After base change to the maximal unramified extension, the image of the
integral points of a supplied model with connected reductive special fibre is
the one-group stabilizer of a special point of every supplied upstairs building
quotient, and that point is the only one it fixes (Bruhat–Tits II,
Propositions 4.6.31, 4.6.28(i) and 4.6.29(i)). -/
def UnramifiedSpecialStabilizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G),
      ∃ x : C.ReducedBuilding, C.IsSpecialPoint x ∧
        M.baseChangeUnramified.integralPoints = C.oneStabilizer x ∧
        ∀ y : C.ReducedBuilding,
          (∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
            g ∈ M.baseChangeUnramified.integralPoints → g • y = y) → y = x

end Langlands.GroupScheme.IntegralModel
