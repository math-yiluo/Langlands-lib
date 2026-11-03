import Langlands.GroupScheme.Absolute.ParabolicIntersectionGeometryStatement
import Langlands.GroupScheme.Dynamic.ParabolicIntersection
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Parabolic pairs from a common maximal torus and the two-parabolic geometry -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Two homomorphisms `j : P ⟶ G` and `j' : P' ⟶ G` over a field form a *common-torus
parabolic pair* when one maximal torus `t : T ⟶ G` and two cocharacters `ν, ν'` of `T` have
the ranges of `j` and `j'` as their dynamic parabolics `P(ν ≫ t)` and `P(ν' ≫ t)`. -/
def IsCommonTorusParabolicPair {K : Type u} [Field K]
    {G P P' : GroupScheme (Spec (CommRingCat.of K))} (j : P ⟶ G) (j' : P' ⟶ G) : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of K))) (t : T.toGrp ⟶ G)
    (ν ν' : cocharacterLattice T),
    IsMaximalTorus t ∧
      SubgroupFunctor.range j = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) ∧
      SubgroupFunctor.range j' = Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t)

/-- **Reduction of the two-parabolic geometry.** Assume dynamic connectedness, and assume that
for any two parabolics `j, j'` of a connected reductive `G` over a field `k`, the base changes
of `j` and `j'` to `AlgebraicClosure k` form a common-torus parabolic pair. Then the actual
intersection of `j` and `j'` is smooth, geometrically connected, and geometrically contains an
ambient maximal torus. -/
theorem parabolicIntersectionGeometry_of_commonTorus
    (hCo : DynamicConnectedStatement.{u})
    (hTorus : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G →
      ∀ (P P' : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (j' : P' ⟶ G),
        IsParabolicSubgroup j → IsParabolicSubgroup j' →
        IsCommonTorusParabolicPair ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)
          ((GroupScheme.baseChange (toAlgebraicClosure k)).map j')) :
    ParabolicIntersectionGeometryStatement.{u} := by
  intro k _ G hG P P' j j' hj hj'
  obtain ⟨T, t, ν, ν', ht, hr, hr'⟩ := hTorus k G hG P P' j j' hj hj'
  have hrep : (SubgroupFunctor.range j ⊓ SubgroupFunctor.range j').IsRepresentedBy
      (pullback.fst j j' ≫ j) :=
    isRepresentedBy_subgroupIntersectionHom hj.isClosedSubgroup hj'.isClosedSubgroup
  have hrepK : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t)).IsRepresentedBy
        ((GroupScheme.baseChange (toAlgebraicClosure k)).map (pullback.fst j j' ≫ j)) := by
    have := hrep.baseChange (toAlgebraicClosure k)
    rwa [SubgroupFunctor.inf_baseChange, ← SubgroupFunctor.range_baseChangeHom,
      ← SubgroupFunctor.range_baseChangeHom, hr, hr'] at this
  have := hG.smooth
  have := hG.isAffineHom
  have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have hle : SubgroupFunctor.range (CommGroupScheme.groupHom ν' ≫ t) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) :=
    (SubgroupFunctor.range_comp_le _ t).trans (range_le_parabolic_groupHom_comp t ν)
  obtain ⟨hsm, hcon⟩ :=
    smooth_connected_of_isRepresentedBy_parabolic_inf hCo _ _ hle hrepK
  have hTle : SubgroupFunctor.range t ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) ⊓
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t) :=
    fun U x hx => ⟨range_le_parabolic_groupHom_comp t ν U hx,
      range_le_parabolic_groupHom_comp t ν' U hx⟩
  refine ⟨?_, hcon hG.connectedSpace_toAlgebraicClosure,
    T, hrepK.liftOfLE t hTle, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := (pullback j j').X.hom) (g := toAlgebraicClosure k) ⟨⟨h1, h2⟩, h3⟩ hsm
  · rw [hrepK.liftOfLE_comp]
    exact ht

end Langlands.GroupScheme
