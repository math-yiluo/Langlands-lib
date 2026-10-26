import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Ideal.Operations

/-! The prime-order orbit product expansion with an ideal-square trace witness. -/

namespace Langlands.LocalClassField

universe u v

/-- The abstract finite-group step of Serre V.3, Lemma 5: for a group of prime order
acting on a commutative ring and an invariant ideal `I`, the conjugate product of
`1 + x` with `x ∈ I` differs from `1 + ∑ g, g • x + ∏ g, g • x` by the orbit sum
of an element of `I ^ 2`. -/
def PrimeOrbitProductTraceExpansion : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] (R : Type v) [CommRing R] [MulSemiringAction G R],
    Nat.Prime (Fintype.card G) →
      ∀ (I : Ideal R), (∀ (g : G) (y : R), y ∈ I → g • y ∈ I) →
        ∀ x : R, x ∈ I →
          ∃ z : R, z ∈ I ^ 2 ∧
            (∏ g : G, (1 + g • x)) - 1 - (∑ g : G, g • x) - (∏ g : G, g • x) =
              ∑ g : G, g • z

end Langlands.LocalClassField
