import Langlands.Global.Adelic
import Langlands.HarmonicAnalysis.Basic
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Additive self-duality and the diagonal annihilator of the actual adeles

Weil, *Basic Number Theory*, second edition (1973), Chapter IV, §2,
Theorem 3, specialized to the one-dimensional vector space `E = K`.
See the paired Markdown for the source correspondence and group conventions.
-/

universe u

namespace Langlands.Global

/-- Every continuous nontrivial additive character of the actual adeles that is
trivial on the diagonal field identifies the additive adele group with its full
Pontryagin dual by multiplication, and the diagonal field is its own annihilator. -/
def AdelicAdditiveDualityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)),
    (∀ x : K, ψ (diagonal K x) = 1) →
      (∃ e : Multiplicative (Adeles K) ≃ₜ*
          PontryaginDual (Multiplicative (Adeles K)),
        ∀ a x : Multiplicative (Adeles K),
          e a x = ψ (Multiplicative.toAdd a * Multiplicative.toAdd x)) ∧
      (∀ a : Adeles K,
        (∀ x : K, ψ (a * diagonal K x) = 1) ↔
          a ∈ Set.range (diagonal K))

end Langlands.Global
