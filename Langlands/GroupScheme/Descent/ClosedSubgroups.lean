import Langlands.GroupScheme.Descent.AffineDatumMorphisms
import Langlands.GroupScheme.Descent.ComponentCoverLifts
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleCrossEmbedding

/-! # Effective descent of invariant affine closed subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}} {p : S ⟶ B} {H G : GroupScheme S} {i : H ⟶ G}

/-- A lift of the ambient overlap through a closed subgroup automatically satisfies
its cocycle: equality can be checked after the monic inclusion. -/
theorem cocycle_of_closedSubgroup_lift (D : Datum p G) (hi : IsClosedSubgroup i)
    (e : OverlapIso p H)
    (he : e.hom ≫ (GroupScheme.baseChange (snd p)).map i =
      (GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom) : Cocycle e := by
  have h12 := pullHom_lift_fac (p12 p) rfl rfl D.overlap e.hom he
  have h23 := pullHom_lift_fac (p23 p) (p23_fst p) rfl D.overlap e.hom he
  have h13 := pullHom_lift_fac (p13 p) (p13_fst p) (p13_snd p) D.overlap e.hom he
  change (iso12 e).hom ≫ (GroupScheme.baseChange (p2 p)).map i =
    (GroupScheme.baseChange (p1 p)).map i ≫ (iso12 D.overlap).hom at h12
  change (iso23 e).hom ≫ (GroupScheme.baseChange (p3 p)).map i =
    (GroupScheme.baseChange (p2 p)).map i ≫ (iso23 D.overlap).hom at h23
  change (iso13 e).hom ≫ (GroupScheme.baseChange (p3 p)).map i =
    (GroupScheme.baseChange (p1 p)).map i ≫ (iso13 D.overlap).hom at h13
  have hc : ((iso12 e).hom ≫ (iso23 e).hom) ≫ (GroupScheme.baseChange (p3 p)).map i =
      (iso13 e).hom ≫ (GroupScheme.baseChange (p3 p)).map i := by
    rw [Category.assoc, h23, ← Category.assoc, h12, Category.assoc, D.cocycle, h13]
  let : IsClosedImmersion ((GroupScheme.baseChange (p3 p)).map i).hom.hom.left :=
    hi.baseChange (p3 p)
  let : Mono ((GroupScheme.baseChange (p3 p)).map i).hom.hom := Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono ((GroupScheme.baseChange (p3 p)).map i).hom.hom).mp
  exact congrArg (fun a => a.hom.hom) hc

namespace Datum

variable (D : Datum p G) (hi : IsClosedSubgroup i)
    (h : SubgroupFunctor.range ((GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i))

/-- Equal all-test images give the actual source overlap isomorphism. -/
def closedSubgroupOverlap : OverlapIso p H :=
  ((hi.baseChange (fst p)).comp_iso D.overlap).sourceIsoOfRangeEq
    (hi.baseChange (snd p)) h

/-- The constructed source overlap respects the actual inclusions. -/
theorem closedSubgroupOverlap_fac :
    (D.closedSubgroupOverlap hi h).hom ≫ (GroupScheme.baseChange (snd p)).map i =
      (GroupScheme.baseChange (fst p)).map i ≫ D.overlap.hom :=
  IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ h

/-- An invariant closed subgroup inherits actual descent data, including its cocycle. -/
def closedSubgroup : Datum p H where
  overlap := D.closedSubgroupOverlap hi h
  cocycle := cocycle_of_closedSubgroup_lift D hi _ (D.closedSubgroupOverlap_fac hi h)

/-- The original closed inclusion is compatible with the inherited data. -/
theorem compatible_closedSubgroup : Compatible (D.closedSubgroup hi h) D i :=
  (D.closedSubgroupOverlap_fac hi h).symm

end Datum

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme

/-- Closedness of a homomorphism of affine group schemes is detected by flat,
surjective pullback between affine bases. -/
theorem IsClosedSubgroup.of_baseChange_of_isAffine
    {B S : Scheme.{u}} (p : S ⟶ B) [IsAffine B] [IsAffine S]
    [Flat p] [Surjective p] {H G : GroupScheme B}
    [IsAffine H.X.left] [IsAffine G.X.left] {i : H ⟶ G}
    (hi : IsClosedSubgroup ((GroupScheme.baseChange p).map i)) : IsClosedSubgroup i := by
  let : IsClosedImmersion ((GroupScheme.baseChange p).map i).hom.hom.left := hi
  have houter : IsPullback
      (((GroupScheme.baseChange p).map i).hom.hom.left ≫ pullback.snd G.X.hom p)
      (pullback.fst H.X.hom p) p (i.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback p).map i.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w i.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback H.X.hom p).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange p).map i).hom.hom.left ≫ pullback.fst G.X.hom p =
        pullback.fst H.X.hom p ≫ i.hom.hom.left by
      change ((Over.pullback p).map i.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom p).flip
  let : IsAffine ((GroupScheme.baseChange p).obj H).X.left := by
    change IsAffine (pullback H.X.hom p)
    infer_instance
  let : IsAffine ((GroupScheme.baseChange p).obj G).X.left := by
    change IsAffine (pullback G.X.hom p)
    infer_instance
  exact Langlands.AlgebraicGeometry.isClosedImmersion_of_isPullback_of_affine_fpqc hp

open Descent

/-- An all-test invariant closed subgroup of the pullback of an affine group
has an actual affine closed-subgroup descent, with exact pullback recovery. -/
theorem IsClosedSubgroup.exists_descent_of_overlap_range_eq
    {B S : Scheme.{u}} (p : S ⟶ B) [IsAffine B] [IsAffine S]
    [Flat p] [Surjective p] {C : GroupScheme B} [IsAffine C.X.left]
    {H : GroupScheme S} {i : H ⟶ (GroupScheme.baseChange p).obj C}
    (hi : IsClosedSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst p)).map i ≫ (canonicalOverlap p C).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange (snd p)).map i)) :
    ∃ (H₀ : GroupScheme B) (j : H₀ ⟶ C) (e : (GroupScheme.baseChange p).obj H₀ ≅ H),
      IsAffine H₀.X.left ∧ IsClosedSubgroup j ∧
        (GroupScheme.baseChange p).map j = e.hom ≫ i := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffine ((GroupScheme.baseChange p).obj C).X.left := by
    change IsAffine (pullback C.X.hom p)
    infer_instance
  let : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  let D := (canonicalDatum p C).closedSubgroup hi h
  have hcompat : Compatible D (canonicalDatum p C) i :=
    (canonicalDatum p C).compatible_closedSubgroup hi h
  let j := D.affineHomTo C i hcompat
  have hj : (GroupScheme.baseChange p).map j = D.affineSolution.iso.hom ≫ i :=
    D.baseChange_affineHomTo C i hcompat
  refine ⟨D.affineSolution.obj, j, D.affineSolution.iso, inferInstance, ?_, hj⟩
  apply IsClosedSubgroup.of_baseChange_of_isAffine p
  rw [hj]
  exact (IsClosedSubgroup.of_iso D.affineSolution.iso).comp hi

end Langlands.GroupScheme
