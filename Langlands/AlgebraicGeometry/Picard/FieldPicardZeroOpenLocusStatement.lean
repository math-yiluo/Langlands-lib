import Langlands.AlgebraicGeometry.Picard.OpenLocus
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Existence of the geometric Picard-zero open locus over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- A locally finite type parameter scheme with an actual universal rigidified family
has an open locus characterized by geometric Picard-zero classes on every test scheme. -/
def FieldPicardZeroOpenLocusStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P),
    LocallyOfFiniteType P.hom →
      RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L →
        ∃ U : P.left.Opens, IsPicardZeroOpenLocus A L U

end Langlands.AbelianScheme
