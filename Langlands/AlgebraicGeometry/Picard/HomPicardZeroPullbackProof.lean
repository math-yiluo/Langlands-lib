import Langlands.AlgebraicGeometry.Picard.HomPicardZeroPullbackStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackComparison

/-! # Homomorphism pullback preserves geometric Picard zero -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} {A B : AbelianScheme S}

private lemma hom_baseChange_fst (f : A ⟶ B) {V : Scheme.{u}} (s : V ⟶ S) :
    hom ((baseChange s).map f) ≫ pullback.fst B.X.hom s =
      pullback.fst A.X.hom s ≫ hom f := by
  change ((Over.pullback s).map (groupHom f).hom.hom).left ≫ _ = _
  simp

/-- Geometric translation invariance pulls back along an abelian-scheme homomorphism. -/
lemma isGeometricallyPicardZero_homPullback (f : A ⟶ B) {L : LineBundle B.X.left}
    (hL : IsGeometricallyPicardZero B L) :
    IsGeometricallyPicardZero A ((LineBundle.pullback (hom f)).obj L) := by
  intro K _ _ s
  apply GroupScheme.isTranslationInvariant_of_iso _ (L :=
    (LineBundle.pullback (hom ((baseChange s).map f))).obj (fibreLineBundle B L s))
  · change (LineBundle.pullback (hom ((baseChange s).map f))).obj
        ((LineBundle.pullback (pullback.fst B.X.hom s)).obj L) ≅
      (LineBundle.pullback (pullback.fst A.X.hom s)).obj
        ((LineBundle.pullback (hom f)).obj L)
    exact (LineBundle.pullbackComp _ _).app L ≪≫
      eqToIso (congrArg (fun k ↦ (LineBundle.pullback k).obj L) (hom_baseChange_fst f s)) ≪≫
      ((LineBundle.pullbackComp _ _).app L).symm
  · exact GroupScheme.isTranslationInvariant_pullback (groupHom ((baseChange s).map f))
      (hL K s)

private lemma hom_baseChange_symmetry (f : A ⟶ B) (T : Over S) :
    hom ((baseChange T.hom).map f) ≫ (relativeSpaceSymmetry B.X.hom T).inv =
      (relativeSpaceSymmetry A.X.hom T).inv ≫ (homFamilySpaceMap f).app T := by
  apply pullback.hom_ext
  · simp [relativeSpaceSymmetry, Category.assoc]
    exact (groupHom ((baseChange T.hom).map f)).hom.hom.w
  · simp [relativeSpaceSymmetry, Category.assoc, hom_baseChange_fst]

/-- Forgetting rigidification and changing the product order commutes with homomorphism pullback. -/
def homFamilyLineBundleIso (f : A ⟶ B) (T : Over S) (L : RigidifiedFamily B T) :
    (LineBundle.pullback (hom ((baseChange T.hom).map f))).obj (familyLineBundle B L) ≅
      familyLineBundle A ((homFamilyPullback f T).obj L) := by
  let N := (RigidifiedLineBundle.forget _).obj L
  change (LineBundle.pullback (hom ((baseChange T.hom).map f))).obj
      ((LineBundle.pullback (relativeSpaceSymmetry B.X.hom T).inv).obj N) ≅
    (LineBundle.pullback (relativeSpaceSymmetry A.X.hom T).inv).obj
      ((LineBundle.pullback ((homFamilySpaceMap f).app T)).obj N)
  exact (LineBundle.pullbackComp _ _).app N ≪≫
    eqToIso (congrArg (fun k ↦ (LineBundle.pullback k).obj N) (hom_baseChange_symmetry f T)) ≪≫
    ((LineBundle.pullbackComp _ _).app N).symm

/-- The exact geometric Picard-zero preservation statement. -/
theorem homPicardZeroPullback : HomPicardZeroPullbackStatement.{u} := by
  intro S A B f T L hL
  exact isGeometricallyPicardZero_of_iso _ (homFamilyLineBundleIso f T L)
    (isGeometricallyPicardZero_homPullback ((baseChange T.hom).map f) hL)

end Langlands.AbelianScheme
