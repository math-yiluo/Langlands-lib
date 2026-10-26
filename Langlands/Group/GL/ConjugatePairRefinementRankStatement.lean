import Langlands.Representation.Exponents.ParabolicPair

/-! Strict refinement of concrete conjugate block pairs increases block length.
This is a closed proposition definition, not a proof of the geometry. -/

namespace Langlands

universe uF

/-- Actual strict refinement increases the number of positive blocks, which
is bounded by the ambient rank, over every infinite field. -/
def ConjugatePairRefinementRankStatement : Prop :=
  ∀ (K : Type uF) [Field K] [Infinite K] (n : ℕ),
    (∀ P Q : Exponents.ConjugateBlockPair n K,
      Q.StrictlyRefines P → P.shape.length < Q.shape.length) ∧
    (∀ P : Exponents.ConjugateBlockPair n K, P.shape.length ≤ n)

end Langlands
