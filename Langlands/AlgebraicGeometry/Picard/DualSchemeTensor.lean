import Langlands.AlgebraicGeometry.Picard.TensorNaturality
import Langlands.AlgebraicGeometry.Picard.DualSchemeOrigin
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorSymmetry
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # Tensor multiplication on a chosen dual parameter scheme -/

universe u

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable (stability : PicardZeroPullbackStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- The actual Picard-zero class classified by a point of the chosen dual. -/
def dualPointClass {T : Over S} (f : T ⟶ dualScheme A hA) : PicardZeroClasses A T :=
  picardZeroClassifyingMap A stability (poincareFamily A hA)
    (poincareFamily_universal A hA).1 T f

lemma dualPointClass_classify (T : Over S) (q : PicardZeroClasses A T) :
    dualPointClass stability A hA (dualClassify A hA T q) = q := by
  apply Subtype.ext
  exact dualClassify_spec A hA T q

lemma dualClassify_pointClass {T : Over S} (f : T ⟶ dualScheme A hA) :
    dualClassify A hA T (dualPointClass stability A hA f) = f := by
  symm
  apply dualClassify_unique
  rfl

lemma dualPointClass_comp {T U : Over S} (f : T ⟶ U) (g : U ⟶ dualScheme A hA) :
    dualPointClass stability A hA (f ≫ g) =
      picardZeroClassesPullback stability A f (dualPointClass stability A hA g) :=
  picardZeroClassifyingMap_comp A stability RigidifiedModule.pullbackCoherence
    (poincareFamily A hA) (poincareFamily_universal A hA).1 f g

lemma dualPointClass_injective (T : Over S) :
    Function.Injective (dualPointClass stability A hA (T := T)) :=
  (picardZeroClassifyingMap_bijective A stability (poincareFamily A hA)
    (poincareFamily_universal A hA) T).1

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Multiplication on the chosen dual classifies the tensor of the two universal pullbacks. -/
def dualTensor : dualScheme A hA ⨯ dualScheme A hA ⟶ dualScheme A hA :=
  dualClassify A hA (dualScheme A hA ⨯ dualScheme A hA)
    (picardZeroClassesTensor preservation A _
      (dualPointClass stability A hA prod.fst)
      (dualPointClass stability A hA prod.snd))

lemma dualTensor_spec :
    dualPointClass stability A hA (dualTensor stability A hA preservation) =
      picardZeroClassesTensor preservation A _
        (dualPointClass stability A hA prod.fst)
        (dualPointClass stability A hA prod.snd) :=
  dualPointClass_classify stability A hA _ _

variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorLeftUnitorStatement.{u})

include composition unitCoherence in
/-- On every test scheme, the constructed multiplication induces actual tensor of classes. -/
lemma dualTensor_points {T : Over S} (f g : T ⟶ dualScheme A hA) :
    dualPointClass stability A hA (prod.lift f g ≫ dualTensor stability A hA preservation) =
      picardZeroClassesTensor preservation A T
        (dualPointClass stability A hA f) (dualPointClass stability A hA g) := by
  rw [dualPointClass_comp, dualTensor_spec,
    picardZeroClassesPullback_tensor preservation composition unitCoherence,
    ← dualPointClass_comp, ← dualPointClass_comp, prod.lift_fst, prod.lift_snd]

include composition unitCoherence in
/-- Tensor classification agrees with multiplication of the two classifying points. -/
lemma dualClassify_tensor (T : Over S) (q r : PicardZeroClasses A T) :
    dualClassify A hA T (picardZeroClassesTensor preservation A T q r) =
      prod.lift (dualClassify A hA T q) (dualClassify A hA T r) ≫
        dualTensor stability A hA preservation := by
  apply dualPointClass_injective stability A hA T
  rw [dualPointClass_classify, dualTensor_points stability A hA preservation composition unitCoherence,
    dualPointClass_classify, dualPointClass_classify]

/-- A base pullback of the distinguished origin classifies the trivial family. -/
lemma dualPointClass_origin (T : Over S) :
    dualPointClass stability A hA
        ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) =
      trivialPicardZeroClass A T := by
  rw [← dualClassify_trivial stability A hA T, dualPointClass_classify]

include composition in
/-- The distinguished origin is a left unit for the constructed multiplication. -/
lemma dualTensor_left_unit (twoUnitCoherence : PullbackTensorUnitCoherenceStatement.{u}) :
    prod.lift
        ((Over.homMk (dualScheme A hA).hom : dualScheme A hA ⟶ Over.mk (𝟙 S)) ≫
          dualOrigin A hA) (𝟙 (dualScheme A hA)) ≫ dualTensor stability A hA preservation =
      𝟙 (dualScheme A hA) := by
  apply dualPointClass_injective stability A hA
  rw [dualTensor_points stability A hA preservation composition twoUnitCoherence.1,
    dualPointClass_origin, picardZeroClassesTensor_left_unit preservation A twoUnitCoherence]

include composition in
/-- The distinguished origin is a right unit for the constructed multiplication. -/
lemma dualTensor_right_unit (twoUnitCoherence : PullbackTensorUnitCoherenceStatement.{u}) :
    prod.lift (𝟙 (dualScheme A hA))
        ((Over.homMk (dualScheme A hA).hom : dualScheme A hA ⟶ Over.mk (𝟙 S)) ≫
          dualOrigin A hA) ≫ dualTensor stability A hA preservation =
      𝟙 (dualScheme A hA) := by
  apply dualPointClass_injective stability A hA
  rw [dualTensor_points stability A hA preservation composition twoUnitCoherence.1,
    dualPointClass_origin, picardZeroClassesTensor_right_unit preservation A twoUnitCoherence]

include composition unitCoherence in
/-- Multiplication is commutative on every test scheme. -/
lemma dualTensor_points_comm (symmetry : PullbackTensorSymmetryStatement.{u})
    {T : Over S} (f g : T ⟶ dualScheme A hA) :
    prod.lift f g ≫ dualTensor stability A hA preservation =
      prod.lift g f ≫ dualTensor stability A hA preservation := by
  apply dualPointClass_injective stability A hA
  rw [dualTensor_points stability A hA preservation composition unitCoherence,
    dualTensor_points stability A hA preservation composition unitCoherence,
    picardZeroClassesTensor_comm preservation symmetry]

include composition unitCoherence in
/-- Swapping the two scheme factors leaves the multiplication morphism unchanged. -/
lemma dualTensor_comm (symmetry : PullbackTensorSymmetryStatement.{u}) :
    (prod.lift prod.snd prod.fst : dualScheme A hA ⨯ dualScheme A hA ⟶
        dualScheme A hA ⨯ dualScheme A hA) ≫ dualTensor stability A hA preservation =
      dualTensor stability A hA preservation := by
  have h := dualTensor_points_comm stability A hA preservation composition unitCoherence
    symmetry (prod.snd : dualScheme A hA ⨯ dualScheme A hA ⟶ dualScheme A hA) prod.fst
  simpa only [prod.lift_fst_snd, Category.id_comp] using h

end Langlands.AbelianScheme
