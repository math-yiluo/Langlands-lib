import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Cohomology vanishing for nontrivial translation-invariant line bundles over an
algebraically closed field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules

/-- On an abelian scheme over an algebraically closed field `K`, a line bundle that is
invariant under translation by every `K`-point and is not isomorphic to the structure sheaf
has zero `K`-module cohomology `Hⁿ(A, L)` in every degree `n`, including degree zero.
This proposition is a statement target, not a proof. -/
def AlgClosedFieldTranslationInvariantCohomologyVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left),
    GroupScheme.IsTranslationInvariant A.toGrp L →
    ¬ Nonempty (L ≅ LineBundle.trivial A.X.left) →
      ∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj L.obj)

end Langlands.AbelianScheme
