import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Reflection of algebraic simple connectedness along algebraic field extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Algebraic simple connectedness of an actual field group is reflected by base change along
every algebraic field extension `k → K`, with no further hypothesis on the original group. -/
def SimplyConnectedAlgebraicExtensionReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSimplyConnected
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) →
      IsSimplyConnected G

end Langlands.GroupScheme
