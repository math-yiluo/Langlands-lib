import Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A local-dimension lower bound at the origin of a universal rigidified Picard parameter
from a finite rational translation stabilizer -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Let `A` be an abelian scheme of relative dimension `g` over an algebraically closed field
`k`, and let `U` be an actual universal rigidified family on a locally finite type parameter
`P`. If some line bundle `L` on `A` is preserved, up to isomorphism, by only finitely many
rational translations, then the stalk of `P` at the published origin point has Krull
dimension at least `g`.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (U : RigidifiedFamily A P)
    (hU : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) U)
    (g : ℕ),
    LocallyOfFiniteType P.hom → A.HasRelativeDimension g →
      ∀ (L : LineBundle A.X.left),
        Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
          Nonempty ((LineBundle.pullback
            (GroupScheme.translation A.toGrp x).left).obj L ≅ L)} →
        (g : WithBot ℕ∞) ≤
          ringKrullDim (P.left.presheaf.stalk (fullPicardOriginPoint k A U hU))

end Langlands.AbelianScheme
