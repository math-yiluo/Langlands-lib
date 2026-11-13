import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction

/-! # The Iwahori model of a Galois-stable chamber of a simply connected group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme

private instance localUnramifiedIwahoriModelAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **The Iwahori model of a Galois-stable chamber** (Kaletha–Prasad 9.2.5–9.2.6 with
Theorem 8.3.13, 4.1.12(1), Remark 4.1.13 and 9.3.26). Let `F` be a nonarchimedean local field,
`L = inertiaFixedField F` its maximal unramified extension, `Γ = Aut(L/F)` and `G` a
simply connected `F`-group. For any building data `C` of `G_L` with semilinear Galois data
`D` and any chamber `Y₀` of `C` stable under the action of every `σ ∈ Γ`, there is a smooth
integral model `M` of `G` over `𝒪[F]` with connected special fibre whose image of
`𝒪_L`-points in `G(L)` is exactly the stabilizer of `Y₀`. -/
def LocalSimplyConnectedUnramifiedIwahoriModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∀ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (D : MaximalUnramified.SemilinearApartmentData C) (Y₀ : Set C.ReducedBuilding),
      C.IsChamber Y₀ →
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ '' Y₀ = Y₀) →
      ∃ M : IntegralModel 𝒪[F] F G,
        M.IsSmooth ∧
        ConnectedSpace
          ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left ∧
        ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
          g ∈ M.baseChangeUnramified.integralPoints ↔ (g • ·) '' Y₀ = Y₀

end Langlands.GroupScheme
