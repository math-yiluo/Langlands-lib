import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackComparison
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Ground base change preserves and reflects geometric Picard zero -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

/-- Translation invariance is preserved and reflected by a group-scheme isomorphism. -/
lemma isTranslationInvariant_pullback_iso_iff {S : Scheme.{u}}
    {G H : GroupScheme S} (e : G ≅ H) (L : LineBundle H.X.left) :
    IsTranslationInvariant G ((LineBundle.pullback e.hom.hom.hom.left).obj L) ↔
      IsTranslationInvariant H L := by
  constructor
  · intro hL
    have h := isTranslationInvariant_pullback e.inv hL
    have he : e.inv.hom.hom.left ≫ e.hom.hom.hom.left = 𝟙 H.X.left :=
      congrArg (fun f : H ⟶ H ↦ f.hom.hom.left) e.inv_hom_id
    apply isTranslationInvariant_of_iso H _ h
    exact (LineBundle.pullbackComp _ _).app L ≪≫
      eqToIso (congrArg (fun f ↦ (LineBundle.pullback f).obj L) he) ≪≫
      (LineBundle.pullbackId _).app L
  · exact isTranslationInvariant_pullback e.hom

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Geometric translation invariance transports through an isomorphism of underlying groups. -/
lemma isGeometricallyPicardZero_pullback_groupIso_iff {S : Scheme.{u}}
    (A B : AbelianScheme S) (e : A.toGrp ≅ B.toGrp) (L : LineBundle B.X.left) :
    IsGeometricallyPicardZero A ((LineBundle.pullback e.hom.hom.hom.left).obj L) ↔
      IsGeometricallyPicardZero B L := by
  have fibre_iff (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S) :
      GroupScheme.IsTranslationInvariant ((baseChange s).obj A).toGrp
        (fibreLineBundle A ((LineBundle.pullback e.hom.hom.hom.left).obj L) s) ↔
      GroupScheme.IsTranslationInvariant ((baseChange s).obj B).toGrp
        (fibreLineBundle B L s) := by
    let d := (GroupScheme.baseChange s).mapIso e
    have hd : d.hom.hom.hom.left ≫ pullback.fst B.X.hom s =
        pullback.fst A.X.hom s ≫ e.hom.hom.hom.left := by
      change ((Over.pullback s).map e.hom.hom.hom).left ≫ _ = _
      simp
    have c : (LineBundle.pullback d.hom.hom.hom.left).obj (fibreLineBundle B L s) ≅
        fibreLineBundle A ((LineBundle.pullback e.hom.hom.hom.left).obj L) s :=
      (LineBundle.pullbackComp _ _).app L ≪≫
        eqToIso (congrArg (fun f ↦ (LineBundle.pullback f).obj L) hd) ≪≫
        ((LineBundle.pullbackComp _ _).app L).symm
    exact (GroupScheme.isTranslationInvariant_iff_of_iso _ c).symm.trans
      (GroupScheme.isTranslationInvariant_pullback_iso_iff d (fibreLineBundle B L s))
  constructor
  · intro h K _ _ s
    exact (fibre_iff K s).mp (h K s)
  · intro h K _ _ s
    exact (fibre_iff K s).mpr (h K s)

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

/-- Composition of group-scheme base change identifies the two parameter-wise groups. -/
def familyBaseChangeGroupIso (T : Over S') :
    ((baseChange T.hom).obj ((baseChange b).obj A)).toGrp ≅
      ((baseChange ((Over.map b).obj T).hom).obj A).toGrp :=
  (GroupScheme.baseChangeCompIso b T.hom A.toGrp).symm

private lemma familyBaseChangeGroupIso_symmetry (T : Over S') :
    (familyBaseChangeGroupIso b A T).hom.hom.hom.left ≫
        (relativeSpaceSymmetry A.X.hom ((Over.map b).obj T)).inv =
      (relativeSpaceSymmetry ((baseChange b).obj A).X.hom T).inv ≫
        familyBaseChangeSpaceMap b A T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, relativeSpaceSymmetry,
      pullbackSymmetry_inv_comp_fst, familyBaseChangeSpaceMap_fst]
    exact (familyBaseChangeGroupIso b A T).hom.hom.hom.w
  · simp only [Category.assoc, relativeSpaceSymmetry,
      pullbackSymmetry_inv_comp_snd, familyBaseChangeSpaceMap_snd,
      pullbackSymmetry_inv_comp_snd_assoc]
    exact GroupScheme.baseChangeCompIso_inv_fst b T.hom A.toGrp

/-- The group comparison pulls the old family bundle back to the actual new family bundle. -/
def familyBaseChangeLineBundleIso (T : Over S')
    (L : RigidifiedFamily A ((Over.map b).obj T)) :
    (LineBundle.pullback (familyBaseChangeGroupIso b A T).hom.hom.hom.left).obj
        (familyLineBundle A L) ≅
      familyLineBundle ((baseChange b).obj A) ((familyBaseChange b A T).obj L) := by
  let N := (RigidifiedLineBundle.forget _).obj L
  change (LineBundle.pullback (familyBaseChangeGroupIso b A T).hom.hom.hom.left).obj
      ((LineBundle.pullback (relativeSpaceSymmetry A.X.hom ((Over.map b).obj T)).inv).obj N) ≅
    (LineBundle.pullback (relativeSpaceSymmetry ((baseChange b).obj A).X.hom T).inv).obj
      ((LineBundle.pullback (familyBaseChangeSpaceMap b A T)).obj N)
  exact (LineBundle.pullbackComp _ _).app N ≪≫
    eqToIso (congrArg (fun f ↦ (LineBundle.pullback f).obj N)
      (familyBaseChangeGroupIso_symmetry b A T)) ≪≫
    ((LineBundle.pullbackComp _ _).app N).symm

/-- Actual ground-base pullback preserves and reflects the geometric Picard-zero predicate. -/
theorem picardZeroFamilyBaseChange : PicardZeroFamilyBaseChangeStatement.{u} := by
  intro S S' b A T L
  exact (isGeometricallyPicardZero_pullback_groupIso_iff
    ((baseChange T.hom).obj ((baseChange b).obj A))
    ((baseChange ((Over.map b).obj T).hom).obj A)
    (familyBaseChangeGroupIso b A T) (familyLineBundle A L)).symm.trans
      (isGeometricallyPicardZero_iff_of_iso _ (familyBaseChangeLineBundleIso b A T L))

end Langlands.AbelianScheme
