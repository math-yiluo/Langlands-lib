import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteFunctor

/-! # The absolute-Galois character anti-equivalence: statement -/

universe u

open CategoryTheory

namespace Langlands.GroupScheme

/-- The actual separable-closure character functor is an anti-equivalence
between all multiplicative-type groups over a field and finitely generated
discrete integral modules for its absolute Galois group. -/
def MultiplicativeTypeAbsoluteEquivalenceStatement : Prop :=
  ∀ (k : Type u) [Field k],
    (MultiplicativeTypeGroup.characterFunctor k).IsEquivalence

end Langlands.GroupScheme
