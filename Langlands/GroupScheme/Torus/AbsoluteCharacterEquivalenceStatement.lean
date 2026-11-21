import Langlands.GroupScheme.Torus.AbsoluteCharacterFunctor

/-! # The absolute Galois character anti-equivalence for field tori: statement -/

universe u

open CategoryTheory

namespace Langlands.GroupScheme

/-- The actual separable-closure character functor is an anti-equivalence from
field tori to finite free integral modules with continuous discrete absolute
Galois action. -/
def TorusAbsoluteCharacterEquivalenceStatement : Prop :=
  ∀ (k : Type u) [Field k], (FieldTorus.characterFunctor k).IsEquivalence

end Langlands.GroupScheme
