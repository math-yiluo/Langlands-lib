import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Geometric reducedness of a universal rigidified Picard parameter over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over a field, a locally finite type parameter scheme carrying an actual universal rigidified
family for an abelian scheme is geometrically reduced over the field. -/
def FieldRigidifiedPicardParameterGeometricallyReducedStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P),
    RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L →
      LocallyOfFiniteType P.hom → GeometricallyReduced P.hom

end Langlands.AbelianScheme
