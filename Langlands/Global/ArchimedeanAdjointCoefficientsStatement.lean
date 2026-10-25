import Langlands.Global.ArchimedeanAdjoint
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite continuous coefficients for actual enveloping conjugation -/

noncomputable section

universe u

open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Each enveloping element has a finite expansion of all its actual conjugates
in fixed enveloping elements, with globally continuous complex coefficients. -/
def EnvelopingConjugationCoefficientsStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ a : EnvelopingAlgebra K n, ∃ m : ℕ,
    ∃ b : Fin m → EnvelopingAlgebra K n,
    ∃ c : Fin m → C(InfiniteAdelicGL K n, ℂ),
      ∀ g : InfiniteAdelicGL K n,
        envelopingConjugation K n g a = ∑ i, (c i g) • b i

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @EnvelopingConjugationCoefficientsStatement

end Langlands.Global.ArchimedeanGL
