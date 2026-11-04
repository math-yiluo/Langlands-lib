import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.Separable

/-! # Pseudo-reductivity under separable algebraic extension

This module states the separable algebraic case of CGP Proposition 1.1.9(1).
It supplies no proof.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A pseudo-reductive group stays pseudo-reductive after base change along a
separable algebraic field extension. -/
def PseudoReductiveSeparableExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive G →
      IsPseudoReductive
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

end Langlands.GroupScheme
