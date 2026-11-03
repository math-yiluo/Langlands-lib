import Langlands.GroupScheme.Lie.FullLieOpenSubgroup
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Smoothness from a smooth open subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Existence of an actual smooth group scheme included as an open subgroup. -/
def HasSmoothOpenSubgroup {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ H),
    Smooth K.X.hom ∧ IsOpenImmersion j.hom.hom.left

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open MonObj MonoidalCategory CartesianMonoidalCategory in
/-- Over an algebraically closed field, translation propagates a nonempty
smooth locus to every point of a locally finite-type group. -/
theorem smooth_of_nonempty_smoothLocus {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)]
    (hne : (f.smoothLocus : Set G).Nonempty) : Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro h
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints h
    f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hne
    f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f :=
    Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f :=
    Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    GrpObj.mulRight (A := Over.mk f) y'
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using
      congr(($hα).left (IsLocalRing.closedPoint k))
  rw [← hα'] at hy
  change x ∈ α.hom.left ⁻¹ᵁ f.smoothLocus at hy
  rw! [Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy

/-- A smooth open subgroup makes an ambient locally finite-type group smooth
at arbitrary base field and universe. -/
theorem smooth_of_smooth_open_subgroup {k : Type u} [Field k]
    (H K : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom]
    [Smooth K.X.hom] (j : K ⟶ H) [IsOpenImmersion j.hom.hom.left] :
    Smooth H.X.hom := by
  let Ω : Type u := AlgebraicClosure k
  let b : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let H' := (GroupScheme.baseChange b).obj H
  let K' := (GroupScheme.baseChange b).obj K
  let j' : K' ⟶ H' := (GroupScheme.baseChange b).map j
  have : LocallyOfFiniteType H'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd H.X.hom b))
  have : Smooth K'.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd K.X.hom b))
  have : IsOpenImmersion j'.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b j.hom.hom inferInstance
  have : Smooth (j'.hom.hom.left ≫ H'.X.hom) := by
    simpa only [Over.w] using (inferInstance : Smooth K'.X.hom)
  have hne : (H'.X.hom.smoothLocus : Set H'.X.left).Nonempty := by
    let x : K'.X.left := η[K'.X].left (IsLocalRing.closedPoint Ω)
    refine ⟨j'.hom.hom.left x, ?_⟩
    change x ∈ j'.hom.hom.left ⁻¹ᵁ H'.X.hom.smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    trivial
  let : GrpObj (Over.mk H'.X.hom) := H'.grp
  have hs : Smooth H'.X.hom := smooth_of_nonempty_smoothLocus H'.X.hom hne
  obtain ⟨hb1, hb2, hb3⟩ := fieldExtension_fpqc k Ω
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := H.X.hom) (g := b) ⟨⟨hb1, hb2⟩, hb3⟩ hs

/-- Existence of a smooth open subgroup is equivalent to ambient smoothness
for locally finite-type group schemes over a field. -/
theorem hasSmoothOpenSubgroup_iff_smooth {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom] :
    HasSmoothOpenSubgroup H ↔ Smooth H.X.hom := by
  constructor
  · rintro ⟨K, j, hs, ho⟩
    let : Smooth K.X.hom := hs
    let : IsOpenImmersion j.hom.hom.left := ho
    exact smooth_of_smooth_open_subgroup H K j
  · intro hs
    refine ⟨H, 𝟙 H, hs, ?_⟩
    change IsOpenImmersion (𝟙 H.X.left)
    infer_instance

/-- A smooth closed subgroup with full Lie algebra forces smoothness of the
locally finite-type affine ambient group. -/
theorem smooth_of_fullLie_closed_subgroup {k : Type u} [Field k]
    (H K : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType H.X.hom]
    [IsAffineHom H.X.hom] [Smooth K.X.hom]
    (j : K ⟶ H) (hj : IsClosedSubgroup j)
    (hlie : ∀ X : lieKernel H k, ∃ Y : lieKernel K k,
      Y.val ≫ j.hom.hom = X.val) : Smooth H.X.hom := by
  let : IsOpenImmersion j.hom.hom.left := isOpenImmersion_of_fullLie j hj hlie
  exact smooth_of_smooth_open_subgroup H K j

end Langlands.GroupScheme
