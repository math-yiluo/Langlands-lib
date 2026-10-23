import Langlands.AlgebraicGeometry.Picard.DualSchemeTensor

/-! # Dual maps preserve the constructed tensor multiplication -/

universe u

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorLeftUnitorStatement.{u})
variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Homomorphism pullback preserves the actual rigidified tensor via the canonical comparison. -/
def homFamilyPullbackTensorIso (f : A ⟶ B) (T : Over S) (L M : RigidifiedFamily B T) :
    (homFamilyPullback f T).obj (RigidifiedLineBundle.tensor preservation L M) ≅
      RigidifiedLineBundle.tensor preservation
        ((homFamilyPullback f T).obj L) ((homFamilyPullback f T).obj M) :=
  RigidifiedLineBundle.pullbackTensorIso preservation composition unitCoherence
    ((homFamilySpaceMap f).app T) (𝟙 T.left) _ L M

include composition unitCoherence in
/-- The actual pullback map on compatible classes preserves tensor. -/
lemma homClassesPullback_tensor (f : A ⟶ B) (T : Over S) (q r : RigidifiedClasses B T) :
    homClassesPullback f T
        (RigidifiedLineBundle.classesTensor preservation B.X.hom
          (unitSection B) (unitSection_comp B) T q r) =
      RigidifiedLineBundle.classesTensor preservation A.X.hom
        (unitSection A) (unitSection_comp A) T
          (homClassesPullback f T q) (homClassesPullback f T r) := by
  refine Quotient.inductionOn₂ q r (fun L M ↦ ?_)
  exact Quotient.sound ⟨homFamilyPullbackTensorIso preservation composition unitCoherence f T L M⟩

variable (homPreservation : HomPicardZeroPullbackStatement.{u})

include composition unitCoherence in
/-- Homomorphism pullback preserves tensor on the geometric Picard-zero subtype. -/
lemma homPicardZeroClassesPullback_tensor (f : A ⟶ B) (T : Over S)
    (q r : PicardZeroClasses B T) :
    homPicardZeroClassesPullback homPreservation f T
        (picardZeroClassesTensor preservation B T q r) =
      picardZeroClassesTensor preservation A T
        (homPicardZeroClassesPullback homPreservation f T q)
        (homPicardZeroClassesPullback homPreservation f T r) := by
  apply Subtype.ext
  exact homClassesPullback_tensor preservation composition unitCoherence f T q.val r.val

variable (stability : PicardZeroPullbackStatement.{u})

/-- Composing a point with the dual map classifies its actual homomorphism pullback. -/
lemma dualPointClass_dualSchemeMap (f : A ⟶ B) (hA : HasDualScheme A)
    (hB : HasDualScheme B) {T : Over S} (p : T ⟶ dualScheme B hB) :
    dualPointClass stability A hA (p ≫ dualSchemeMap homPreservation f hA hB) =
      homPicardZeroClassesPullback homPreservation f T (dualPointClass stability B hB p) := by
  have hc := dualSchemeMap_classifies homPreservation RigidifiedModule.pullbackCoherence
    f hA hB T (dualPointClass stability B hB p)
  rw [dualClassify_pointClass] at hc
  rw [← hc, dualPointClass_classify]

include composition unitCoherence in
/-- The constructed dual map preserves the actual multiplication morphism. -/
lemma dualSchemeMap_tensor (f : A ⟶ B) (hA : HasDualScheme A) (hB : HasDualScheme B) :
    dualTensor stability B hB preservation ≫ dualSchemeMap homPreservation f hA hB =
      prod.lift (prod.fst ≫ dualSchemeMap homPreservation f hA hB)
        (prod.snd ≫ dualSchemeMap homPreservation f hA hB) ≫
          dualTensor stability A hA preservation := by
  apply dualPointClass_injective stability A hA
  rw [dualPointClass_dualSchemeMap, dualTensor_spec,
    homPicardZeroClassesPullback_tensor preservation composition unitCoherence,
    dualTensor_points stability A hA preservation composition unitCoherence,
    dualPointClass_dualSchemeMap, dualPointClass_dualSchemeMap]

end Langlands.AbelianScheme
