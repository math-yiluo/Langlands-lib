import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction

/-! # A Galois-stable chamber with an Iwahori model over the maximal unramified extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme

private instance localUnramifiedChamberAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **The chamber input of Kaletha–Prasad, Theorem 10.6.1.** Let `F` be a nonarchimedean local
field, `L = inertiaFixedField F` its maximal unramified extension inside the separable closure,
and `G` a semisimple simply connected group over `F`. There are building data `C` for `G_L` with
a semilinear Galois action `D`, a smooth integral model `M` of `G` over `𝒪[F]` with connected
special fibre, and a chamber `Y₀` of the reduced building of `G_L` such that

* `Y₀` is stable under the Galois action;
* the image of `M(𝒪_L)` in `G(L)` is exactly the stabilizer of `Y₀` (the Iwahori subgroup);
* `G(L)` acts transitively on the chambers;
* for every crossed homomorphism `c : Gal(L/F) → G(L)` that is trivial on the fixing subgroup
  of a finite subextension, some chamber is stable under the twisted action
  `y ↦ c(σ) · σ(y)`. -/
def LocalSimplyConnectedUnramifiedChamberStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∃ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (D : MaximalUnramified.SemilinearApartmentData C)
      (M : IntegralModel 𝒪[F] F G) (Y₀ : Set C.ReducedBuilding),
      M.IsSmooth ∧
      ConnectedSpace ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left ∧
      C.IsChamber Y₀ ∧
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D.action σ '' Y₀ = Y₀) ∧
      (∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
        g ∈ M.baseChangeUnramified.integralPoints ↔ (g • ·) '' Y₀ = Y₀) ∧
      (∀ Y : Set C.ReducedBuilding, C.IsChamber Y →
        ∃ g : rationalPoints (baseChanged F (inertiaFixedField F) G), (g • ·) '' Y₀ = Y) ∧
      ∀ c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
          rationalPoints (baseChanged F (inertiaFixedField F) G),
        (∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ)) →
        (∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
          ∀ σ ∈ E.fixingSubgroup, c σ = 1) →
        ∃ Y : Set C.ReducedBuilding, C.IsChamber Y ∧
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            (fun y => c σ • D.action σ y) '' Y = Y

end Langlands.GroupScheme
