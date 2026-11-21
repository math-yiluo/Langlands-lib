# Truncated tame reduction from the fixed-cutoff average

`Langlands.Henniart.weilTameReductionFromAveraging.{uK,uW}` proves
`WeilTameReductionFromAveragingStatement`. It assumes the fixed-cutoff
averaging identity; it does not prove that identity or an unconditional tame
reduction.

Fix `K`, `r`, `m`, and `j < p^r * m * e_K` as in the truncated target. The
averaging premise supplies an enumeration by `Fin m` and a sum identity at
this `j`. For each enumerated field `L`, the fundamental identity
`PadicField.ramificationIndex_mul_extensionResidueDegree` specializes to
`e_L = m * e_K`: its degree is `m` and its residue degree is `1`. The
relative residue cardinality formula specializes to `q_L = q_K`. Thus
`j < p^r * e_L`, and the target's pure-rank hypothesis at `r' = r` and
`d = m` makes the summand equal to `(q_K - 1) * q_K^j`.

The sum over `Fin m` is now constant, with `m` summands. Left multiplication
by `(m : ℕ∞)` is strictly monotone: the multiplier is finite and nonzero,
the latter because `p ∤ m`. Cancelling it in the sum identity gives the
required count. The cancellation is in `ℕ∞`, so no finiteness hypothesis on
the counts is needed.
