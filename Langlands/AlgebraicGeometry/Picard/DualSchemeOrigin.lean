import Langlands.AlgebraicGeometry.Picard.DualSchemeMap
import Langlands.AlgebraicGeometry.Picard.RigidifiedTrivialPullback

/-! # Trivial families and the origin of the chosen dual -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Homomorphism pullback preserves the actual canonically rigidified trivial family. -/
def homFamilyPullbackTrivialIso (f : A ⟶ B) (T : Over S) :
    (homFamilyPullback f T).obj
        (RigidifiedLineBundle.trivial
          ((relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app T)) ≅
      RigidifiedLineBundle.trivial
        ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T) :=
  RigidifiedLineBundle.pullbackTrivialIso ((homFamilySpaceMap f).app T) (𝟙 T.left) _

lemma homClassesPullback_trivial (f : A ⟶ B) (T : Over S) :
    homClassesPullback f T (trivialPicardZeroClass B T).val =
      (trivialPicardZeroClass A T).val :=
  Quotient.sound ⟨homFamilyPullbackTrivialIso f T⟩

lemma homPicardZeroClassesPullback_trivial
    (preservation : HomPicardZeroPullbackStatement.{u}) (f : A ⟶ B) (T : Over S) :
    homPicardZeroClassesPullback preservation f T (trivialPicardZeroClass B T) =
      trivialPicardZeroClass A T := by
  apply Subtype.ext
  exact homClassesPullback_trivial f T

lemma picardZeroClassesPullback_trivial (stability : PicardZeroPullbackStatement.{u})
    (A : AbelianScheme S) {T U : Over S} (h : T ⟶ U) :
    picardZeroClassesPullback stability A h (trivialPicardZeroClass A U) =
      trivialPicardZeroClass A T := by
  apply Subtype.ext
  exact Quotient.sound ⟨RigidifiedLineBundle.pullbackTrivialIso
    ((relativeSpace A.X.hom).map h) h.left _⟩

/-- Classifying a trivial family is pullback of the distinguished origin section. -/
lemma dualClassify_trivial (stability : PicardZeroPullbackStatement.{u})
    (A : AbelianScheme S) (hA : HasDualScheme A) (T : Over S) :
    dualClassify A hA T (trivialPicardZeroClass A T) =
      Over.homMk T.hom ≫ dualOrigin A hA := by
  have h := dualClassify_pullback A RigidifiedModule.pullbackCoherence stability hA
    (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S))
    (trivialPicardZeroClass A (Over.mk (𝟙 S)))
  rw [picardZeroClassesPullback_trivial] at h
  exact h

/-- The constructed dual map preserves the distinguished origin section. -/
lemma dualSchemeMap_origin (preservation : HomPicardZeroPullbackStatement.{u})
    (f : A ⟶ B) (hA : HasDualScheme A) (hB : HasDualScheme B) :
    dualOrigin B hB ≫ dualSchemeMap preservation f hA hB = dualOrigin A hA := by
  have h := dualSchemeMap_classifies preservation RigidifiedModule.pullbackCoherence
    f hA hB (Over.mk (𝟙 S)) (trivialPicardZeroClass B (Over.mk (𝟙 S)))
  rw [homPicardZeroClassesPullback_trivial] at h
  exact h.symm

end Langlands.AbelianScheme
