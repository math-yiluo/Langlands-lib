import Langlands.AlgebraicGeometry.Picard.RelativePicardZero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A group homomorphism intertwines the translations by corresponding sections. -/
lemma translation_hom (f : G ⟶ H) (x : Over.mk (𝟙 S) ⟶ G.X) :
    translation G x ≫ f.hom.hom =
      f.hom.hom ≫ translation H (x ≫ f.hom.hom) := by
  rw [points_translation, translation, MonObj.mul_comp, Category.id_comp]
  simp only [Category.assoc]

/-- Translation invariance pulls back along every homomorphism over a fixed base. -/
lemma isTranslationInvariant_pullback (f : G ⟶ H) {L : LineBundle H.X.left}
    (hL : IsTranslationInvariant H L) :
    IsTranslationInvariant G ((LineBundle.pullback f.hom.hom.left).obj L) := by
  intro x
  obtain ⟨e⟩ := hL (x ≫ f.hom.hom)
  have comm : (translation G x).left ≫ f.hom.hom.left =
      f.hom.hom.left ≫ (translation H (x ≫ f.hom.hom)).left :=
    congrArg (fun k ↦ k.left) (translation_hom f x)
  refine ⟨(LineBundle.pullbackComp _ _).app L ≪≫ ?_ ≪≫
    ((LineBundle.pullbackComp _ _).app L).symm ≪≫
    (LineBundle.pullback f.hom.hom.left).mapIso e⟩
  exact eqToIso (congrArg (fun k ↦ (LineBundle.pullback k).obj L) comm)

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S) {T U : Over S} (h : T ⟶ U)
  {V : Scheme.{u}} (s : V ⟶ T.left)

/-- The fibre comparison commutes with the actual maps into the relative family. -/
lemma fibreComparison_relative_map
    (m : ((baseChange s).obj ((baseChange T.hom).obj A)).toGrp ⟶
      ((baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj A)).toGrp)
    (hm : m.hom.hom.left ≫ pullback.fst (pullback.snd A.X.hom U.hom) (s ≫ h.left) ≫
      pullback.fst A.X.hom U.hom =
      pullback.fst (pullback.snd A.X.hom T.hom) s ≫ pullback.fst A.X.hom T.hom) :
    m.hom.hom.left ≫ pullback.fst (pullback.snd A.X.hom U.hom) (s ≫ h.left) ≫
        (relativeSpaceSymmetry A.X.hom U).inv =
      pullback.fst (pullback.snd A.X.hom T.hom) s ≫
        (relativeSpaceSymmetry A.X.hom T).inv ≫ (relativeSpace A.X.hom).map h := by
  have mw : m.hom.hom.left ≫
      pullback.snd (pullback.snd A.X.hom U.hom) (s ≫ h.left) =
      pullback.snd (pullback.snd A.X.hom T.hom) s := m.hom.hom.w
  apply pullback.hom_ext
  · simp only [relativeSpaceSymmetry, relativeSpace, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left, Category.assoc, pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_fst_assoc,
      pullback.lift_fst]
    rw [pullback.condition, pullback.condition_assoc, ← Category.assoc, mw]
  · simpa only [relativeSpaceSymmetry, relativeSpace, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left, Category.assoc, pullbackSymmetry_inv_comp_snd,
      pullback.lift_snd] using hm

/-- The two fibre restrictions correspond along a comparison preserving projection to A. -/
def fibreComparison_lineBundleIso
    (m : ((baseChange s).obj ((baseChange T.hom).obj A)).toGrp ⟶
      ((baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj A)).toGrp)
    (hm : m.hom.hom.left ≫ pullback.fst (pullback.snd A.X.hom U.hom) (s ≫ h.left) ≫
      pullback.fst A.X.hom U.hom =
      pullback.fst (pullback.snd A.X.hom T.hom) s ≫ pullback.fst A.X.hom T.hom)
    (L : RigidifiedFamily A U) :
    (LineBundle.pullback m.hom.hom.left).obj
      (fibreLineBundle ((baseChange U.hom).obj A) (familyLineBundle A L) (s ≫ h.left)) ≅
    fibreLineBundle ((baseChange T.hom).obj A)
      (familyLineBundle A ((RigidifiedLineBundle.relativePullback A.X.hom
        (unitSection A) (unitSection_comp A) h).obj L)) s := by
  let N := (RigidifiedLineBundle.forget _).obj L
  let p := pullback.fst (pullback.snd A.X.hom T.hom) s
  let q := pullback.fst (pullback.snd A.X.hom U.hom) (s ≫ h.left)
  let a := (relativeSpaceSymmetry A.X.hom T).inv
  let b := (relativeSpaceSymmetry A.X.hom U).inv
  let r := (relativeSpace A.X.hom).map h
  change (LineBundle.pullback m.hom.hom.left).obj
      ((LineBundle.pullback q).obj ((LineBundle.pullback b).obj N)) ≅
    (LineBundle.pullback p).obj ((LineBundle.pullback a).obj
      ((LineBundle.pullback r).obj N))
  refine (LineBundle.pullback m.hom.hom.left).mapIso ((LineBundle.pullbackComp q b).app N) ≪≫
    (LineBundle.pullbackComp m.hom.hom.left (q ≫ b)).app N ≪≫ ?_ ≪≫
    ((LineBundle.pullbackComp (p ≫ a) r).app N).symm ≪≫
    ((LineBundle.pullbackComp p a).app ((LineBundle.pullback r).obj N)).symm
  exact eqToIso (congrArg (fun k ↦ (LineBundle.pullback k).obj N)
    ((fibreComparison_relative_map A h s m hm).trans (Category.assoc p a r).symm))

/-- A compatible fibre homomorphism transfers invariance to the actual relative pullback. -/
lemma isTranslationInvariant_fibre_relativePullback
    (m : ((baseChange s).obj ((baseChange T.hom).obj A)).toGrp ⟶
      ((baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj A)).toGrp)
    (hm : m.hom.hom.left ≫ pullback.fst (pullback.snd A.X.hom U.hom) (s ≫ h.left) ≫
      pullback.fst A.X.hom U.hom =
      pullback.fst (pullback.snd A.X.hom T.hom) s ≫ pullback.fst A.X.hom T.hom)
    (L : RigidifiedFamily A U)
    (hL : GroupScheme.IsTranslationInvariant
      ((baseChange (s ≫ h.left)).obj ((baseChange U.hom).obj A)).toGrp
      (fibreLineBundle ((baseChange U.hom).obj A) (familyLineBundle A L) (s ≫ h.left))) :
    GroupScheme.IsTranslationInvariant ((baseChange s).obj ((baseChange T.hom).obj A)).toGrp
      (fibreLineBundle ((baseChange T.hom).obj A)
        (familyLineBundle A ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) h).obj L)) s) :=
  GroupScheme.isTranslationInvariant_of_iso _ (fibreComparison_lineBundleIso A h s m hm L)
    (GroupScheme.isTranslationInvariant_pullback m hL)

end Langlands.AbelianScheme
