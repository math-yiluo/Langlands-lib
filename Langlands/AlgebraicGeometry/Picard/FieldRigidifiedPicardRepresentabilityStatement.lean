import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Full rigidified Picard representability over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- All rigidified line-bundle classes on an abelian variety are represented by an
actual universal bundle on a parameter scheme locally of finite type over the field. -/
def FieldRigidifiedPicardRepresentabilityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))),
    ∃ (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
      (L : RigidifiedFamily A P),
      LocallyOfFiniteType P.hom ∧
        RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L

end Langlands.AbelianScheme
