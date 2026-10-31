import Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent
import Langlands.AlgebraicGeometry.PointTangentSpace
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The actual tangent-to-H1 statement for a universal rigidified Picard parameter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands Langlands.AbelianScheme Langlands.AlgebraicGeometry.Picard

/-- At the section classifying the trivial rigidified family, the actual tangent module of
a locally finite type universal parameter is linearly equivalent to structure-sheaf H1. -/
def FieldUniversalRigidifiedPicardTangentH1Statement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (U : RigidifiedFamily A P)
    (hU : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) U),
    LocallyOfFiniteType P.hom →
      let e := RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
        (unitSection_comp A) U hU
      let T := Langlands.Scheme.tangentSpaceAtPoint P e
      let H := (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
        A.X.hom 1).obj (Langlands.Scheme.Modules.structureSheaf A.X.left)
      Nonempty (T ≃ₗ[k] H)

end Langlands.AbelianScheme
