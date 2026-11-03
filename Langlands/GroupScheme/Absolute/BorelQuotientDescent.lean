import Langlands.GroupScheme.ConnectedKernelGeometry
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Borel subgroups descend through cartesian quotient squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Overgroup

variable {S : Scheme.{u}} {B G BQ Q H : GroupScheme S}
    (i : B ⟶ G) (q : G ⟶ Q) (p : B ⟶ BQ) (j : BQ ⟶ Q)
    (hcomm : i ≫ q = p ≫ j) (j' : H ⟶ Q) (f : BQ ⟶ H)
    (hf : f ≫ j' = j)

/-- A factorization of the quotient subgroup through an overgroup pulls back
to an actual homomorphism from the original subgroup into the overgroup preimage. -/
def quotientOvergroupHom : B ⟶ SubgroupPreimage.groupScheme q j' :=
  pullback.lift i (p ≫ f) (by rw [Category.assoc, hf]; exact hcomm)

/-- The lifted homomorphism factors the original subgroup embedding. -/
theorem quotientOvergroupHom_inclusion :
    quotientOvergroupHom i q p j hcomm j' f hf ≫
      SubgroupPreimage.inclusion q j' = i :=
  pullback.lift_fst _ _ _

/-- The lifted homomorphism projects to the given quotient factorization. -/
theorem quotientOvergroupHom_projection :
    quotientOvergroupHom i q p j hcomm j' f hf ≫
      SubgroupPreimage.projection q j' = p ≫ f :=
  pullback.lift_snd _ _ _

end Overgroup

variable {k : Type u} [Field k] [IsAlgClosed k]
    {B G BQ Q : GroupScheme (Spec (CommRingCat.of k))}

/-- In a cartesian square of group schemes, a Borel subgroup descends along
a smooth surjective quasi-compact geometrically connected ambient map. -/
theorem isBorelSubgroup_of_quotient_square
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (q : G ⟶ Q) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left] [GeometricallyConnected q.hom.hom.left]
    (p : B ⟶ BQ) [Smooth p.hom.hom.left] [Surjective p.hom.hom.left]
    (j : BQ ⟶ Q) (hj : IsClosedSubgroup j)
    (hpb : IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom) :
    IsBorelSubgroup j := by
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points B).mp hi.isSolvableGroupScheme
  have : Smooth (p.hom.hom.left ≫ BQ.X.hom) := by
    rw [Over.w p.hom.hom]
    infer_instance
  have hBQ : Smooth BQ.X.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
      p.hom.hom.left BQ.X.hom
  let pPoints : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ BQ.X) :=
    ((yonedaGrp.map p).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
  refine ⟨hj, hBQ,
    (inferInstance : Surjective p.hom.hom.left).surj.connectedSpace
      p.hom.hom.left.continuous,
    (isSolvableGroupScheme_iff_isSolvable_points BQ).mpr
      (Group.isSolvable_of_surjective (f := pPoints) (rationalPoints_surjective p)), ?_⟩
  intro H j' f hj' hHs hHc hHv hf
  have : Smooth H.X.hom := hHs
  have : ConnectedSpace H.X.left := hHc
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points H).mp hHv
  let P := SubgroupPreimage.groupScheme q j'
  let a : P ⟶ G := SubgroupPreimage.inclusion q j'
  let r : P ⟶ H := SubgroupPreimage.projection q j'
  have ha : IsClosedSubgroup a := SubgroupPreimage.isClosedSubgroup q j' hj'
  have : IsClosedImmersion a.hom.hom.left := ha
  have : Mono a.hom.hom := Over.mono_of_mono_left _
  have : Smooth P.X.hom := SubgroupPreimage.smooth q j'
  have : ConnectedSpace P.X.left := SubgroupPreimage.connectedSpace q j'
  have hcomm : i ≫ q = p ≫ j := by
    apply Grp.hom_ext
    exact hpb.w
  let fB : B ⟶ P := quotientOvergroupHom i q p j hcomm j' f hf
  have hfac : fB ≫ a = i := quotientOvergroupHom_inclusion i q p j hcomm j' f hf
  have hproj : fB ≫ r = p ≫ f := quotientOvergroupHom_projection i q p j hcomm j' f hf
  have hfac' : fB.hom.hom ≫ a.hom.hom = i.hom.hom :=
    congrArg (fun g : B ⟶ G => g.hom.hom) hfac
  have hproj' : fB.hom.hom ≫ r.hom.hom = p.hom.hom ≫ f.hom.hom :=
    congrArg (fun g : B ⟶ H => g.hom.hom) hproj
  have hPsol : IsSolvableGroupScheme P := by
    apply (isSolvableGroupScheme_iff_isSolvable_points P).mpr
    let F : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) →*
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) :=
      ((yonedaGrp.map fB).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
    let R : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) →*
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :=
      ((yonedaGrp.map r).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
    apply Group.isSolvable_of_ker_le_range F R
    intro x hx
    change x ≫ r.hom.hom = 1 at hx
    have hxq : (x ≫ a.hom.hom) ≫ q.hom.hom = 1 ≫ j.hom.hom := by
      rw [Category.assoc, (SubgroupPreimage.isPullback q j').w,
        ← Category.assoc, hx, MonObj.one_comp, MonObj.one_comp]
    let b := hpb.lift (x ≫ a.hom.hom) 1 hxq
    refine ⟨b, ?_⟩
    change b ≫ fB.hom.hom = x
    apply (cancel_mono a.hom.hom).mp
    rw [Category.assoc, hfac']
    exact hpb.lift_fst _ _ _
  have : IsIso fB := hi.maximal P a fB ha inferInstance inferInstance hPsol hfac
  have houter :
      IsPullback (fB.hom.hom ≫ a.hom.hom) p.hom.hom q.hom.hom
        (f.hom.hom ≫ j'.hom.hom) := by
    rw [hfac', ← Grp.comp_hom_hom, hf]
    exact hpb
  have hleft : IsPullback fB.hom.hom p.hom.hom r.hom.hom f.hom.hom :=
    houter.of_right hproj' (SubgroupPreimage.isPullback q j')
  have hlefts : IsPullback fB.hom.hom.left p.hom.hom.left r.hom.hom.left f.hom.hom.left :=
    hleft.map (Over.forget _)
  have : Surjective r.hom.hom.left := SubgroupPreimage.surjective_projection q j'
  have : Flat r.hom.hom.left := SubgroupPreimage.flat_projection q j'
  have : QuasiCompact r.hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j') inferInstance
  have : IsIso f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hlefts ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      (inferInstance : IsIso fB.hom.hom.left)
  have : IsIso ((Over.forget _).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Grp.forget₂Mon _)

end Langlands.GroupScheme
