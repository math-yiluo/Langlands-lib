import Langlands.AlgebraicGeometry.Picard.SquareTheorem
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeMapAdditivityStatement

/-! # Additivity of the dual scheme maps -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

include preservation in
/-- Relative pullback preserves the tensor product of rigidified classes. Since every
relative family has the projection as a retraction of its section, an isomorphism of the
underlying line bundles suffices, so no coherence of the tensor comparison is needed. -/
lemma classesPullback_tensor_of_retraction {T U : Over S} (h : T ⟶ U)
    (q r : Classes f ε section_eq U) :
    classesPullback f ε section_eq h (classesTensor preservation f ε section_eq U q r) =
      classesTensor preservation f ε section_eq T
        (classesPullback f ε section_eq h q) (classesPullback f ε section_eq h r) := by
  refine Quotient.inductionOn₂ q r (fun L M ↦ ?_)
  let := preservation ((relativeSpace f).map h)
  exact Quotient.sound ⟨isoOfCarrierIso preservation ((relativeProjection f).app T)
    (relativeSection_projection f ε section_eq T)
    ((asIso (pullbackTensorComparison ((relativeSpace f).map h))).app
      (L.obj.carrier, M.obj.carrier))⟩

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (classification : PicardZeroLineBundleClassificationStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable (globalFunctions : Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions.{u})
variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Pullback preserves the tensor product of Picard-zero classes. -/
lemma picardZeroClassesPullback_tensor_of_preservation (A : AbelianScheme S) {T U : Over S}
    (h : T ⟶ U) (q r : PicardZeroClasses A U) :
    picardZeroClassesPullback stability A h (picardZeroClassesTensor preservation A U q r) =
      picardZeroClassesTensor preservation A T
        (picardZeroClassesPullback stability A h q) (picardZeroClassesPullback stability A h r) :=
  Subtype.ext (RigidifiedLineBundle.classesPullback_tensor_of_retraction preservation
    A.X.hom (unitSection A) (unitSection_comp A) h q.val r.val)

/-- On every test scheme, the constructed multiplication induces the tensor of classes. -/
lemma dualTensor_points_of_preservation (A : AbelianScheme S) (hA : HasDualScheme A)
    {T : Over S} (f g : T ⟶ dualScheme A hA) :
    dualPointClass stability A hA (prod.lift f g ≫ dualTensor stability A hA preservation) =
      picardZeroClassesTensor preservation A T
        (dualPointClass stability A hA f) (dualPointClass stability A hA g) := by
  rw [dualPointClass_comp, dualTensor_spec,
    picardZeroClassesPullback_tensor_of_preservation preservation stability,
    ← dualPointClass_comp, ← dualPointClass_comp, prod.lift_fst, prod.lift_snd]

/-- Tensor classification agrees with multiplication of the two classifying points. -/
lemma dualClassify_tensor_of_preservation (A : AbelianScheme S) (hA : HasDualScheme A)
    (T : Over S) (q r : PicardZeroClasses A T) :
    dualClassify A hA T (picardZeroClassesTensor preservation A T q r) =
      prod.lift (dualClassify A hA T q) (dualClassify A hA T r) ≫
        dualTensor stability A hA preservation := by
  apply dualPointClass_injective stability A hA T
  rw [dualPointClass_classify, dualTensor_points_of_preservation preservation stability,
    dualPointClass_classify, dualPointClass_classify]

/-- The map `T ×_S A ⟶ T ×_S B` induced by a homomorphism is the point with
components the projection to `T` and the composite of the projection to `A` with the
homomorphism. -/
lemma homFamilySpaceMap_app_eq (f : A ⟶ B) (T : Over S) :
    (homFamilySpaceMap f).app T =
      (pairOver B (relativeFst A T) (relativeSnd A T ≫ (groupHom f).hom.hom)).left :=
  rfl

/-- Composing with a sum of homomorphisms multiplies the composites. -/
lemma relativeSnd_comp_add (f g : A ⟶ B) (T : Over S) :
    relativeSnd A T ≫ (groupHom (f + g)).hom.hom =
      (relativeSnd A T ≫ (groupHom f).hom.hom) * (relativeSnd A T ≫ (groupHom g).hom.hom) :=
  (congrArg (relativeSnd A T ≫ ·)
    (rfl : (groupHom (f + g)).hom.hom = (groupHom f).hom.hom * (groupHom g).hom.hom)).trans
      (MonObj.comp_mul _ _ _)

include classification stability globalFunctions in
/-- Pullback of Picard-zero classes along a sum of homomorphisms is the tensor product
of the two pullbacks. -/
theorem homPicardZeroClassesPullback_add (hB : HasDualScheme B) (f g : A ⟶ B) (T : Over S)
    (q : PicardZeroClasses B T) :
    homPicardZeroClassesPullback homPicardZeroPullback (f + g) T q =
      picardZeroClassesTensor preservation A T
        (homPicardZeroClassesPullback homPicardZeroPullback f T q)
        (homPicardZeroClassesPullback homPicardZeroPullback g T q) := by
  rcases q with ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | h L =>
    apply Subtype.ext
    obtain ⟨e⟩ := nonempty_pullback_pairOver_mul_iso preservation classification stability
      globalFunctions B hB L hq (relativeFst A T) (relativeSnd A T ≫ (groupHom f).hom.hom)
      (relativeSnd A T ≫ (groupHom g).hom.hom)
    rw [← relativeSnd_comp_add] at e
    exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso preservation
      ((relativeProjection A.X.hom).app T)
      (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T) e)

include classification globalFunctions in
/-- Dualization carries a sum of homomorphisms to the product of the dual maps under the
constructed tensor multiplication, over an arbitrary base. -/
theorem dualSchemeMap_add (hA : HasDualScheme A) (hB : HasDualScheme B) (f g : A ⟶ B) :
    dualSchemeMap homPicardZeroPullback (f + g) hA hB =
      prod.lift (dualSchemeMap homPicardZeroPullback f hA hB)
        (dualSchemeMap homPicardZeroPullback g hA hB) ≫
          dualTensor stability A hA preservation := by
  let q : PicardZeroClasses B (dualScheme B hB) :=
    ⟨RigidifiedLineBundle.classOf B.X.hom (unitSection B) (unitSection_comp B)
      (poincareFamily B hB), (poincareFamily_universal B hB).1⟩
  have h := dualClassify_tensor_of_preservation preservation stability A hA (dualScheme B hB)
    (homPicardZeroClassesPullback homPicardZeroPullback f _ q)
    (homPicardZeroClassesPullback homPicardZeroPullback g _ q)
  rw [← homPicardZeroClassesPullback_add preservation classification stability globalFunctions
    hB f g _ q] at h
  exact h

include classification globalFunctions in
/-- The field case, conditional on the normalized classification and relative global
functions. -/
theorem fieldDualSchemeMapAdditivity_of_classification :
    FieldDualSchemeMapAdditivityStatement.{u} := by
  intro preservation stability k _ A B hA hB f g
  exact dualSchemeMap_add preservation classification stability globalFunctions hA hB f g

end Langlands.AbelianScheme
