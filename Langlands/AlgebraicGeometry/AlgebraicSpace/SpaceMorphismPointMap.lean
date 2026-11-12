import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasPointTopology
import Mathlib.Topology.ContinuousMap.Basic

/-! # Continuity and surjectivity of algebraic-space point maps -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology IsLocalRing

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Points

/-- A target's surjective étale scheme atlas makes every presheaf transformation
into it continuous for the point topologies. -/
theorem continuous_map_of_atlas {F G : Presheaf S} (f : F ⟶ G) {V : Over S}
    (a : (schemeYoneda S).obj V ⟶ G) (ha : IsEtale a) (hs : IsSurjective a) :
    Continuous[pointTopology F, pointTopology G] (map f) := by
  let := pointTopology G
  rw [continuous_pointTopology_iff]
  intro U b _
  let hr := ha.representable
  have he : Etale (hr.snd (b ≫ f)).left :=
    ha.projection (b ≫ f) (hr.fst (b ≫ f)) (hr.snd (b ≫ f)) (hr.isPullback (b ≫ f))
  have hsur : Surjective (hr.snd (b ≫ f)).left :=
    hs.projection (b ≫ f) (hr.fst (b ≫ f)) (hr.snd (b ≫ f)) (hr.isPullback (b ≫ f))
  let := he
  have hquot := (hr.snd (b ≫ f)).left.isOpenMap.isQuotientMap
    (hr.snd (b ≫ f)).left.continuous hsur.surj
  apply hquot.continuous_iff.mpr
  have hw : (map f ∘ map b ∘ schemePoint U) ∘ (hr.snd (b ≫ f)).left =
      chartPointMap a ∘ (hr.fst' (b ≫ f)).left := by
    funext t
    change map f (map b (schemePoint U ((hr.snd (b ≫ f)).left t))) = _
    rw [← map_comp]
    exact (chartPointMap_comm (hr.isPullback' (b ≫ f)).w t).symm
  rw [hw]
  exact (continuous_schemePoint_chart a ha).comp (hr.fst' (b ≫ f)).left.continuous

/-- A representable geometrically surjective transformation is surjective
on the quotient point sets. -/
theorem surjective_map {F G : Presheaf S} {f : F ⟶ G} (hf : IsSurjective f) :
    Function.Surjective (map f) := by
  intro z
  induction z using Quot.ind with
  | _ p =>
    let b : (schemeYoneda S).obj (Over.mk p.base) ⟶ G :=
      uliftYonedaEquiv.{u + 1}.symm p.val
    let hr := hf.representable
    have hs : Surjective (hr.snd b).left :=
      hf.projection b (hr.fst b) (hr.snd b) (hr.isPullback b)
    obtain ⟨t, ht⟩ := hs.surj (closedPoint p.field)
    refine ⟨chartPointMap (hr.fst b) t, ?_⟩
    change map f (map (hr.fst b) (schemePoint (hr.pullback b) t)) = _
    rw [← map_comp, (hr.isPullback b).w]
    change chartPointMap ((schemeYoneda S).map (hr.snd b) ≫ b) t = _
    rw [chartPointMap_comp, ht]
    exact chartPointMap_fieldPoint p

/-- Every morphism of algebraic spaces is continuous on its actual point spaces. -/
theorem continuous_map {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Continuous[pointTopology X.presheaf, pointTopology Y.presheaf] (map (hom f)) := by
  obtain ⟨V, a, ha, hs⟩ := Y.property.2
  exact continuous_map_of_atlas (hom f) a ha hs

/-- The continuous map on point spaces induced by an algebraic-space morphism. -/
def spaceContinuousMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    @ContinuousMap (Points X.presheaf) (Points Y.presheaf)
      (pointTopology X.presheaf) (pointTopology Y.presheaf) := by
  letI := pointTopology X.presheaf
  letI := pointTopology Y.presheaf
  exact ⟨map (hom f), continuous_map f⟩

end Points

end Langlands.AlgebraicGeometry.AlgebraicSpace
