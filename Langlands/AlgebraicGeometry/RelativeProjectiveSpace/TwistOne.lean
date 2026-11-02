import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateGenerationOpenProof
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs

/-! # The degree-one twist on relative finite projective space -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false in
lemma pullbackSection_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {h : X ⟶ Z} (w : f ≫ g = h) (M : Z.Modules) (s : GlobalSections M) :
    ((Scheme.Modules.pullbackComp f g).hom.app M ≫
        (Scheme.Modules.pullbackCongr w).hom.app M).app ⊤
        (pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s)) =
      pullbackSection h M s := by
  subst h
  simpa [Scheme.Modules.pullbackCongr] using LinearSystem.pullbackSection_comp M g f s

/-- The actual degree-one twist on the integral polynomial-Proj model, as a line bundle. -/
def integralTwistOne (n : ℕ) : Picard.LineBundle (ProjectiveSpace (ULift.{u} ℤ) n) :=
  ⟨Langlands.AlgebraicGeometry.twistOne (ULift.{u} ℤ) n,
    (projectiveSpaceTwistOneLocalFrames (ULift.{u} ℤ) n).2⟩

/-- The degree-one twist on relative projective space is pulled back from the integral model. -/
def twistOne (S : Scheme.{u}) (n : ℕ) : Picard.LineBundle (RelativeProjectiveSpace S n) :=
  (Picard.LineBundle.pullback (toIntegral S n)).obj (integralTwistOne n)

/-- The canonical comparison of the degree-one twists for a change of base. -/
def twistOnePullbackIso (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    (Picard.LineBundle.pullback (map n f)).obj (twistOne T n) ≅ twistOne S n :=
  ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackComp (map n f) (toIntegral T n)).app (integralTwistOne n).obj ≪≫
      (Scheme.Modules.pullbackCongr (map_toIntegral n f)).app (integralTwistOne n).obj)

/-- The twist on the actual Cartesian pullback agrees with the twist over the new base. -/
def baseChangeTwistOneIso (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    (Picard.LineBundle.pullback (baseChangeIso n f).hom).obj
        ((Picard.LineBundle.pullback (pullback.snd f (toBase T n))).obj (twistOne T n)) ≅
      twistOne S n :=
  (Picard.LineBundle.pullbackComp (baseChangeIso n f).hom
    (pullback.snd f (toBase T n))).app (twistOne T n) ≪≫
      (ObjectProperty.isoMk _
        ((Scheme.Modules.pullbackCongr (baseChangeIso_hom_snd n f)).app
          (twistOne T n).obj) :
        (Picard.LineBundle.pullback
          ((baseChangeIso n f).hom ≫ pullback.snd f (toBase T n))).obj (twistOne T n) ≅
        (Picard.LineBundle.pullback (map n f)).obj (twistOne T n)) ≪≫ twistOnePullbackIso n f

/-- The homogeneous coordinate section pulled back from the actual integral twist. -/
def twistOneCoordinate (S : Scheme.{u}) (n : ℕ) (i : Fin (n + 1)) :
    GlobalSections (twistOne S n).obj :=
  pullbackSection (toIntegral S n) (integralTwistOne n).obj
    (Langlands.AlgebraicGeometry.twistOneCoordinate (ULift.{u} ℤ) n i)

/-- The canonical twist comparison takes each pulled-back coordinate to that coordinate. -/
lemma twistOnePullbackIso_coordinate (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T)
    (i : Fin (n + 1)) :
    (twistOnePullbackIso n f).hom.hom.app ⊤
        (pullbackSection (map n f) (twistOne T n).obj (twistOneCoordinate T n i)) =
      twistOneCoordinate S n i := by
  exact pullbackSection_comp_eq (map n f) (toIntegral T n) (map_toIntegral n f)
    (integralTwistOne n).obj
    (Langlands.AlgebraicGeometry.twistOneCoordinate (ULift.{u} ℤ) n i)

set_option backward.isDefEq.respectTransparency false in
/-- The Cartesian twist comparison also preserves the actual coordinate sections. -/
lemma baseChangeTwistOneIso_coordinate (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T)
    (i : Fin (n + 1)) :
    (baseChangeTwistOneIso n f).hom.hom.app ⊤
        (pullbackSection (baseChangeIso n f).hom
          ((Scheme.Modules.pullback (pullback.snd f (toBase T n))).obj (twistOne T n).obj)
          (pullbackSection (pullback.snd f (toBase T n)) (twistOne T n).obj
            (twistOneCoordinate T n i))) =
      twistOneCoordinate S n i := by
  change (twistOnePullbackIso n f).hom.hom.app ⊤
    (((Scheme.Modules.pullbackComp (baseChangeIso n f).hom
        (pullback.snd f (toBase T n))).hom.app (twistOne T n).obj ≫
      (Scheme.Modules.pullbackCongr (baseChangeIso_hom_snd n f)).hom.app
        (twistOne T n).obj).app ⊤ _) = _
  rw [pullbackSection_comp_eq, twistOnePullbackIso_coordinate]

/-- The relative coordinate chart is the inverse image of the integral coordinate chart. -/
def coordinateOpen (S : Scheme.{u}) (n : ℕ) (i : Fin (n + 1)) :
    (RelativeProjectiveSpace S n).Opens :=
  (toIntegral S n) ⁻¹ᵁ projectiveSpaceCoordinateOpen (ULift.{u} ℤ) n i

/-- The relative coordinate charts cover the whole projective space. -/
lemma iSup_coordinateOpen (S : Scheme.{u}) (n : ℕ) :
    (⨆ i : Fin (n + 1), coordinateOpen S n i) = ⊤ :=
  (toIntegral S n).iSup_preimage_eq_top (iSup_projectiveSpaceCoordinateOpen (ULift.{u} ℤ) n)

/-- The whole generation open of a relative coordinate section is its coordinate chart. -/
lemma trivializationOpen_twistOneCoordinate (S : Scheme.{u}) (n : ℕ) (i : Fin (n + 1)) :
    trivializationOpen (twistOne S n).obj (twistOneCoordinate S n i) = coordinateOpen S n i := by
  change trivializationOpen ((Scheme.Modules.pullback (toIntegral S n)).obj
    (integralTwistOne n).obj) (pullbackSection (toIntegral S n) (integralTwistOne n).obj _) = _
  exact (lineBundlePullbackSectionOpen _ _ (toIntegral S n) (integralTwistOne n)
    (Langlands.AlgebraicGeometry.twistOneCoordinate (ULift.{u} ℤ) n i)).trans
      (congrArg (fun U ↦ (toIntegral S n) ⁻¹ᵁ U)
        (projectiveSpaceCoordinateGenerationOpen (ULift.{u} ℤ) n i))

/-- Every relative coordinate section is a frame on its coordinate chart. -/
lemma twistOneCoordinate_trivializesOn (S : Scheme.{u}) (n : ℕ) (i : Fin (n + 1)) :
    TrivializesOn (twistOne S n).obj (twistOneCoordinate S n i) (coordinateOpen S n i) :=
  (maximalTrivialization _ _ _ _).mpr (trivializationOpen_twistOneCoordinate S n i ▸ le_rfl)

/-- Relative coordinate charts commute with every change of base. -/
@[simp]
lemma map_preimage_coordinateOpen (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T)
    (i : Fin (n + 1)) :
    (map n f) ⁻¹ᵁ coordinateOpen T n i = coordinateOpen S n i := by
  rw [coordinateOpen, ← Scheme.Hom.comp_preimage, map_toIntegral, coordinateOpen]

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
