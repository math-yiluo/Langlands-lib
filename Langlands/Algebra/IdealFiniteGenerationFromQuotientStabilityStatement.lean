import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Finite generation from stability of finite quotient approximations -/

universe u v

namespace Langlands.Algebra

/-- The elementary ideal-stabilization step in Stacks tag 05UV, separated from
the flatness arguments that supply its quotient-injectivity hypothesis.
This proposition states the implication; it does not prove it. -/
def IdealFiniteGenerationFromQuotientStabilityStatement : Prop :=
  ∀ (B : Type u) (F : Type v) [CommRing B] [CommRing F]
    (f : B →+* F) (J : Ideal B),
    (J.map f).FG →
    (∀ (I K : Ideal B), I.FG → K.FG → ∀ (hIK : I ≤ K),
      K ≤ J → I.map f = J.map f →
      Function.Injective (Ideal.Quotient.factor hIK)) →
    J.FG

end Langlands.Algebra
