import Langlands.Geometry.Analytic.FieldValuedPoints
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Field.ULift

/-! # Transport of analytic point fields -/

noncomputable section

universe u v w uL uM uN

namespace Langlands.Analytic

namespace PointFieldTransport

variable (F : Type uL) [NormedField F]

/-- The lifted field carries the original norm. -/
instance uliftNormedField : NormedField (ULift.{uN} F) where
  __ : NormedCommRing (ULift.{uN} F) := inferInstance
  __ : Field (ULift.{uN} F) := inferInstance
  norm_mul a b := norm_mul a.down b.down

instance uliftIsUltrametricDist [IsUltrametricDist F] : IsUltrametricDist (ULift.{uN} F) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b =>
    IsUltrametricDist.norm_add_le_max a.down b.down

variable {F} (E : Type uM) [NormedField E] [NormedAlgebra F E]

/-- The scalar action of a lifted field is the original action after `down`. -/
@[instance_reducible]
def liftBaseNormedAlgebra : NormedAlgebra (ULift.{uN} F) E where
  __ : Algebra (ULift.{uN} F) E := ULift.algebra' F E
  norm_smul_le a b := norm_smul_le a.down b

/-- An algebra map out of a lifted source, with its original coefficients. -/
def downAlgHom : ULift.{uN} E →ₐ[F] E := ULift.algEquiv.toAlgHom

@[simp]
theorem downAlgHom_apply (a : ULift.{uN} E) : downAlgHom (F := F) E a = a.down := rfl

/-- An algebra map into a lifted target, with its original coefficients. -/
def upAlgHom : E →ₐ[F] ULift.{uN} E := ULift.algEquiv.symm.toAlgHom

@[simp]
theorem upAlgHom_apply (a : E) : upAlgHom (F := F) E a = ULift.up a := rfl

end PointFieldTransport

namespace AffinoidAtlasPresentation.FieldPoint

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : AffinoidAtlasPresentation.{u, v, w} K}
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {M : Type uM} [NormedField M] [NormedAlgebra K M]

/-- Compose every evaluation of a field-valued point with one isometric algebra map. -/
def mapField (p : AffinoidAtlasPresentation.FieldPoint L A) (f : L →ₐ[K] M)
    (hf : Isometry f) : AffinoidAtlasPresentation.FieldPoint M A where
  point := p.point
  eval i hi := f.comp (p.eval i hi)
  isChartPoint i hi := by
    obtain ⟨q, hq, hn⟩ := p.isChartPoint i hi
    exact ⟨q, hq, fun a =>
      ((AddMonoidHomClass.isometry_iff_norm f).mp hf _).trans (hn a)⟩
  eval_restriction i j hij hi := by
    rw [AlgHom.comp_assoc, p.eval_restriction]

@[simp]
theorem mapField_point (p : AffinoidAtlasPresentation.FieldPoint L A) (f : L →ₐ[K] M)
    (hf : Isometry f) : (p.mapField f hf).point = p.point := rfl

end AffinoidAtlasPresentation.FieldPoint

end Langlands.Analytic
