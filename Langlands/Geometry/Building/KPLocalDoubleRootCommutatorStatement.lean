import Langlands.Geometry.Building.KPLocalMoyPrasadGroups

/-! # The doubled-root commutator estimate over `K = F^ur` (KP 7.1.1, 7.2.3)

Let `B` be building data over the maximal unramified extension `K = F^ur` whose centralizer
`Z = B.centralizer.Z` is a torus (`hZ : IsTorus Z`, the binder convention of
`MaximalUnramified.BuildingData.centralizerTorus`). For nontrivial `u ∈ U_a(K)`,
`u' ∈ U_{-a}(K)` with `u ∈ U_{2a}(K)` or `u' ∈ U_{-2a}(K)` and depth
`r = x_a(u) + x_{-a}(u') > 0`, the `Z`-component of `u'⁻¹ u u' u⁻¹` (KP Definition 7.1.3)
lies in `Z(K)_{2r}`, the published torus filtration `B.centralizerTorusFiltration hZ`.

This is the actual `K`-level analogue of
`ParahoricBuildingData.CentralizerFiltration.IsDoubleRootCommutatorFriendly`. KP do not state
it as a separate result: it is the doubled case of the `SU_3` computation in the quasi-split
proof of KP Proposition 7.1.1, combined with the congruence criterion and functoriality of
the filtration used in the proof of KP Lemma 7.2.3.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- The doubled-root commutator estimate over `K = F^ur`: if `u ∈ U_a(K)*`,
`u' ∈ U_{-a}(K)*`, `u ∈ U_{2a}(K)` or `u' ∈ U_{-2a}(K)`, and
`r = x_a(u) + x_{-a}(u') > 0`, then the `Z`-component `z` of `u'⁻¹ u u' u⁻¹ = v' j(z) v` lies
in `Z(K)_{2r}` (quasi-split proof of KP Proposition 7.1.1, Definition 7.1.3, proof of
Lemma 7.2.3). -/
def KPLocalDoubleRootCommutatorStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z),
    ∀ (x : B.Apartment) (a : relativeRoots B.i) (u u' : rationalPoints H),
      u ∈ B.rootGroup a.1 → u ≠ 1 → u' ∈ B.rootGroup (-a.1) → u' ≠ 1 →
      (u ∈ B.doubleRootGroup a.1 ∨ u' ∈ B.doubleRootGroup (-a.1)) →
      ∀ r : ℝ≥0, 0 < r →
        (((r : ℝ) : WithTop ℝ) = x.val a.1 u + x.val (-a.1) u') →
      ∀ (v' v : rationalPoints H) (z : rationalPoints B.centralizer.Z),
        v' ∈ B.rootGroup (-a.1) → v ∈ B.rootGroup a.1 →
        u'⁻¹ * u * u' * u⁻¹ = v' * rationalPoints.map B.centralizer.j z * v →
        z ∈ B.centralizerTorusFiltration hZ (2 * r)

end Langlands.Geometry.Building
