import Langlands.AlgebraicGeometry.Picard.Ample

/-!
# Twisting by a large power of an ample line bundle

This proposition combines Stacks Proposition 27.13 (1) ⇒ (7) (tag 01QA) with
Lemma 27.5 (tag 0890): for an ample `H` and any line bundle `N`, every actual line
bundle isomorphic to `N ⊗ H^{⊗b}` is ample once `b` is large. Its proof is a
separate obligation.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- For an ample line bundle `H` and any line bundle `N`, there is `b₀` such that every
actual line bundle isomorphic to `N ⊗ H^{⊗b}` with `b₀ ≤ b` is ample. -/
def AmplePowerTwistStatement : Prop :=
  ∀ (X : Scheme.{u}) (H N : LineBundle X), H.IsAmple →
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      ∀ P : LineBundle X,
        Nonempty (P.obj ≅ tensorObj N.obj (tensorPow H.obj b)) → P.IsAmple

end Langlands.AlgebraicGeometry.Picard
