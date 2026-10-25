# Uniformizer proof of real-exponent faithfulness

This module proves the focused statement
`Langlands.LeviRealPowerFaithfulnessStatement.{uF}`. Its exact-target theorem is
`Langlands.leviRealPowerFaithfulness.{uF}`.

The implemented proof evaluates the published block-scalar character formula
at `Pi.mulSingle i (uniformizerUnit T)`. All factors except `i` are one. The
uniformizer absolute-value formula at integer power `1` identifies the
remaining base with `q⁻¹`. The real-power multiplication law converts its
`B.size i * t i` power into `q ^ (-(B.size i : ℝ) * t i)`.

For restricted-character injectivity, the proof applies the equality of
monoid homomorphisms to that unit tuple, then coerces to `ℂ`. The evaluation
formula and injectivity of the embedding `ℝ → ℂ` give equality of real powers
of `q`. Since `q > 1`, `Real.rpow_right_inj` gives equality of their exponents.
Every block has positive size; cancellation therefore gives `t i = u i`.
Function extensionality finishes the vector equality. The proof works for
the empty index type without a separate positive-rank hypothesis.

Full-character injectivity follows by composing the equality with
`B.blockScalarLevi F.Carrier` and using the restricted result. The two
`eq_iff` lemmas package these injectivity statements as equality criteria.
The final theorem assembles uniformizer evaluation and both injectivity
conclusions in exactly the proposition's order.

The proof uses the published normalized absolute value, block scalar map, and
real determinant characters without changing their definitions. It imposes
no chamber or sum-zero restriction and retains the central direction,
including one-block shapes. Its provenance is the elementary argument from
these definitions and Mathlib's real-power identities; no external
classification theorem is used.
