import Langlands.Geometry.Building.FilteredRootProducts
import Langlands.Geometry.Building.KPLocalMoyPrasadGroups

/-!
# KP Lemma 7.2.3 over `K = F^ur` for the torus filtration of quasi-split building data

For building data `B` over the maximal unramified extension `K = F^ur` whose centralizer
`Z = B.centralizer.Z` is a torus (`hZ : IsTorus B.centralizer.Z`), the filtration
`Z(K)_r = B.centralizerTorusFiltration hZ r` (the published `localTorusFiltration` of `Z`)
is commutator friendly (KP Definition 7.2.1 and Lemma 7.2.3), root compatible and stable
under conjugation by `N(K)`. These are the `K`-level copies of the predicates
`IsCommutatorFriendly`, `IsRootCompatible` and `IsNormalizerStable` of
`ParahoricBuildingData.CentralizerFiltration`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- KP Lemma 7.2.3 over `K = F^ur`, with `Z(K)_r = B.centralizerTorusFiltration hZ r` and
`j(Z(K)_r) = B.centralizerTorusImage hZ r`:

1. commutator friendliness (the commutator clause of KP Definition 7.2.1): for `u ∈ U_a(K)*`,
   `u' ∈ U_{-a}(K)*` and `x` with `r = x_a(u) + x_{-a}(u') > 0`, every `Z`-component `z` of
   `u'⁻¹ u u' u⁻¹ = v' · j(z) · v` (`v' ∈ U_{-a}(K)`, `v ∈ U_a(K)`) lies in `Z(K)_r`;
2. root compatibility: for `z ∈ j(Z(K)_r)` and `u ∈ U_{a,x,s}`, the commutator
   `z u z⁻¹ u⁻¹` lies in the block `U_{a,x,r+s} U_{2a,x,r+s}`;
3. `N(K)`-stability: conjugation by `n ∈ N(K)` maps `j(Z(K)_r)` onto itself.

The sharper `2r` bound for double roots is deliberately not part of this statement. -/
def QuasiSplitLocalTorusFiltrationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z),
    (∀ (x : B.Apartment) (a : relativeRoots B.i) (u u' : rationalPoints H),
      u ∈ B.rootGroup a.1 → u ≠ 1 → u' ∈ B.rootGroup (-a.1) → u' ≠ 1 →
      ∀ r : ℝ≥0, 0 < r → (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
      ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
        v' ∈ B.rootGroup (-a.1) → v ∈ B.rootGroup a.1 →
        u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
        z ∈ B.centralizerTorusFiltration hZ r) ∧
    (∀ (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0),
      ∀ z ∈ B.centralizerTorusImage hZ r, ∀ u ∈ B.filtration x a.1 s,
        z * u * z⁻¹ * u⁻¹ ∈
          B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1) ∧
    (∀ n ∈ normalizerPoints B.i, ∀ r : ℝ≥0,
      (B.centralizerTorusImage hZ r).map (MulAut.conj n).toMonoidHom =
        B.centralizerTorusImage hZ r)

end Langlands.Geometry.Building
