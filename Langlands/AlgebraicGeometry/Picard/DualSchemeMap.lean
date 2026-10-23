import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.HomFamilyNaturality

/-! # The contravariant map between chosen dual parameter schemes -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} {A B C : AbelianScheme S}
variable (preservation : HomPicardZeroPullbackStatement.{u})

/-- Classify the actual homomorphism pullback of the Poincaré family. -/
def dualSchemeMap (f : A ⟶ B) (hA : HasDualScheme A) (hB : HasDualScheme B) :
    dualScheme B hB ⟶ dualScheme A hA :=
  dualClassify A hA (dualScheme B hB)
    (homPicardZeroClassesPullback preservation f (dualScheme B hB)
      ⟨RigidifiedLineBundle.classOf B.X.hom (unitSection B) (unitSection_comp B)
        (poincareFamily B hB), (poincareFamily_universal B hB).1⟩)

lemma dualSchemeMap_spec (f : A ⟶ B) (hA : HasDualScheme A) (hB : HasDualScheme B) :
    RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) (dualScheme B hB) (dualSchemeMap preservation f hA hB) =
    homClassesPullback f (dualScheme B hB)
      (RigidifiedLineBundle.classOf B.X.hom (unitSection B) (unitSection_comp B)
        (poincareFamily B hB)) :=
  dualClassify_spec A hA _ _

/-- The defining comparison is an actual isomorphism of rigidified line bundles. -/
def dualSchemeMapPullbackIso (f : A ⟶ B) (hA : HasDualScheme A) (hB : HasDualScheme B) :
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
      (dualSchemeMap preservation f hA hB)).obj (poincareFamily A hA) ≅
      (homFamilyPullback f (dualScheme B hB)).obj (poincareFamily B hB) :=
  Classical.choice
    ((RigidifiedLineBundle.classifyingMap_eq_iff A.X.hom (unitSection A)
      (unitSection_comp A) (poincareFamily A hA)
      ((homFamilyPullback f (dualScheme B hB)).obj (poincareFamily B hB)) _).mp
      (dualSchemeMap_spec preservation f hA hB))

variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})

include coherence in
/-- The map induces homomorphism pullback on every rigidified Picard-zero class. -/
lemma dualSchemeMap_classifies (f : A ⟶ B) (hA : HasDualScheme A)
    (hB : HasDualScheme B) (T : Over S) (q : PicardZeroClasses B T) :
    dualClassify A hA T (homPicardZeroClassesPullback preservation f T q) =
      dualClassify B hB T q ≫ dualSchemeMap preservation f hA hB := by
  symm
  apply dualClassify_unique
  rw [RigidifiedLineBundle.classifyingMap_comp A.X.hom
    (unitSection A) (unitSection_comp A) coherence, dualSchemeMap_spec,
    homClassesPullback_naturality coherence]
  change homClassesPullback f T
    (RigidifiedLineBundle.classifyingMap B.X.hom (unitSection B) (unitSection_comp B)
      (poincareFamily B hB) T (dualClassify B hB T q)) = _
  rw [dualClassify_spec]
  rfl

include coherence in
lemma dualSchemeMap_id (A : AbelianScheme S) (hA : HasDualScheme A) :
    dualSchemeMap preservation (𝟙 A) hA hA = 𝟙 (dualScheme A hA) := by
  unfold dualSchemeMap
  rw [homPicardZeroClassesPullback_id coherence]
  exact dualClassify_poincare A coherence hA

include coherence in
lemma dualSchemeMap_comp (f : A ⟶ B) (g : B ⟶ C)
    (hA : HasDualScheme A) (hB : HasDualScheme B) (hC : HasDualScheme C) :
    dualSchemeMap preservation (f ≫ g) hA hC =
      dualSchemeMap preservation g hB hC ≫ dualSchemeMap preservation f hA hB := by
  unfold dualSchemeMap
  rw [homPicardZeroClassesPullback_comp coherence]
  exact dualSchemeMap_classifies preservation coherence f hA hB _ _

end Langlands.AbelianScheme
