import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Higher-cohomology vanishing for ample line bundles on abelian varieties over an
algebraically closed field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules

/-- On an abelian scheme over an algebraically closed field `K`, an ample line bundle has
zero `K`-module cohomology `Hⁱ(A, L)` in every positive degree `i`. Degree zero is not
constrained. This proposition is a statement target, not a proof. -/
def AmpleLineBundleHigherCohomologyVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L : LineBundle A.X.left), L.IsAmple →
      ∀ i : ℕ, 0 < i → IsZero ((DerivedSections.relativeCohomology A.X.hom i).obj L.obj)

end Langlands.AbelianScheme
