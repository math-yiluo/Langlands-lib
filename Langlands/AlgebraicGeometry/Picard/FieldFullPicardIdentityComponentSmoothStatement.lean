import Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent
import Langlands.AlgebraicGeometry.Picard.OpenLocus
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness of a supplied identity-component open of a full Picard parameter over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- For a locally finite type parameter scheme carrying an actual universal rigidified family
over a field, every supplied open whose carrier is the connected component of the origin point
is smooth over the field as an actual open subscheme. -/
def FieldFullPicardIdentityComponentSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P)
    (hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L),
    LocallyOfFiniteType P.hom →
      ∀ U : P.left.Opens,
        IsFullPicardIdentityComponentOpen k A L hL U →
          Smooth (openLocusParameter P U).hom

end Langlands.AbelianScheme
