import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.GroupScheme.GaloisPointRational

/-! # A Galois-fixed building point fixed by the bounded points of a maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance torusUnitGaloisFixedPointAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **A Galois-fixed point of the building over `F^ur` fixed by `S(K)^1`** (KP
Proposition 7.9.5 and corrected §9.2.1, as used in the proof of KP Proposition 9.3.4).
Let `F` be a nonarchimedean local field, `K = inertiaFixedField F` its maximal
unramified extension with normalized valuation, `G` a connected reductive `F`-group
and `iS : S → G` a maximal `F`-split torus. Then there are building data `C` of `G_K`
over `K`, a group homomorphism `ρ` from `Gal(K/F)` to the permutations of the
reduced building of `C`, and a point `y` of that building such that

* each `ρ σ` is `σ`-semilinear: `ρ σ (g • z) = σ(g) • ρ σ z` for `g ∈ G(K)`;
* `y` is fixed by every `ρ σ`; and
* every point of `S_K(K)` in the common valuation kernel of its rational characters
  (the bounded subgroup `S(K)^1`) fixes `y`. -/
def UnramifiedTorusUnitGaloisFixedPointStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
    IsMaximalSplitTorus iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∃ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (ρ : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →*
        Equiv.Perm C.ReducedBuilding)
      (y : C.ReducedBuilding),
      (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
        (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
        (z : C.ReducedBuilding),
        ρ σ (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • ρ σ z) ∧
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, ρ σ y = y) ∧
      IsFixedByUnramifiedTorusUnits F iS y

end Langlands.Geometry.Building
