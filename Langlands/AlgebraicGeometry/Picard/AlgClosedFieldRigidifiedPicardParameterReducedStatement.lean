import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Reducedness of a universal rigidified Picard parameter over an algebraically closed
field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over an algebraically closed field, a locally finite type parameter scheme carrying an
actual universal rigidified family for an abelian scheme is reduced.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldRigidifiedPicardParameterReducedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P),
    RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L →
      LocallyOfFiniteType P.hom → IsReduced P.left

end Langlands.AbelianScheme
