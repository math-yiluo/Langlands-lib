import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroTensor
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorUnit

/-! # Tensor on relative geometric Picard-zero classes -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include preservation in
/-- Tensoring two rigidified Picard-zero families preserves the geometric condition. -/
lemma isPicardZeroFamily_tensor {T : Over S} {L M : RigidifiedFamily A T}
    (hL : IsPicardZeroFamily A L) (hM : IsPicardZeroFamily A M) :
    IsPicardZeroFamily A (RigidifiedLineBundle.tensor preservation L M) := by
  exact isGeometricallyPicardZero_of_iso _
    (LineBundle.pullbackTensorObjIso preservation (relativeSpaceSymmetry A.X.hom T).inv
      ((RigidifiedLineBundle.forget _).obj L)
      ((RigidifiedLineBundle.forget _).obj M)).symm
    (isGeometricallyPicardZero_tensor preservation _ hL hM)

include preservation in
/-- The tensor operation on rigidified classes preserves Picard-zero membership. -/
lemma isPicardZeroClass_tensor {T : Over S} (q r : RigidifiedClasses A T)
    (hq : IsPicardZeroClass A q) (hr : IsPicardZeroClass A r) :
    IsPicardZeroClass A (RigidifiedLineBundle.classesTensor preservation A.X.hom
      (unitSection A) (unitSection_comp A) T q r) := by
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M => exact isPicardZeroFamily_tensor preservation A hq hr

/-- Restrict the actual tensor operation to relative Picard-zero classes. -/
def picardZeroClassesTensor (T : Over S) :
    PicardZeroClasses A T → PicardZeroClasses A T → PicardZeroClasses A T :=
  fun q r ↦ ⟨RigidifiedLineBundle.classesTensor preservation A.X.hom
    (unitSection A) (unitSection_comp A) T q.val r.val,
    isPicardZeroClass_tensor preservation A q.val r.val q.property r.property⟩

/-- Forgetting membership recovers tensor on all rigidified classes. -/
@[simp] lemma picardZeroClassesTensor_val (T : Over S) (q r : PicardZeroClasses A T) :
    (picardZeroClassesTensor preservation A T q r).val =
      RigidifiedLineBundle.classesTensor preservation A.X.hom
        (unitSection A) (unitSection_comp A) T q.val r.val := rfl

variable (coherence : PullbackTensorUnitCoherenceStatement.{u})

include coherence in
/-- The canonical trivial Picard-zero class is a left tensor unit. -/
lemma picardZeroClassesTensor_left_unit (T : Over S) (q : PicardZeroClasses A T) :
    picardZeroClassesTensor preservation A T (trivialPicardZeroClass A T) q = q := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classesTensor_left_unit preservation coherence
    A.X.hom (unitSection A) (unitSection_comp A) T q.val

include coherence in
/-- The canonical trivial Picard-zero class is a right tensor unit. -/
lemma picardZeroClassesTensor_right_unit (T : Over S) (q : PicardZeroClasses A T) :
    picardZeroClassesTensor preservation A T q (trivialPicardZeroClass A T) = q := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classesTensor_right_unit preservation coherence
    A.X.hom (unitSection A) (unitSection_comp A) T q.val

end Langlands.AbelianScheme
