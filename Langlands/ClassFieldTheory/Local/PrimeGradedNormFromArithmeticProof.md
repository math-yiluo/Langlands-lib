# Conditional proof of all prime graded norm formulas

Author: Worker 96.

`primeGradedNormFromArithmetic` proves exactly
`PrimeGradedNormFromArithmetic.{u,v}`. It assumes proofs of
`PrimeRamifiedTraceIdeals.{u,v}` and `PrimeNormTraceExpansion.{u,v}` and
then establishes the entire unchanged `PrimeRamifiedGradedNorm.{u,v}`
conclusion. The arithmetic propositions remain hypotheses within this
intermediate target. This module does not prove either arithmetic input and
does not provide the closed unconditional theorem required by the host task.
All supplied scalar structures, independent field universes, arbitrary
order-one uniformizers, and actual forward residue maps are retained.

Write `ell = [L:F]`, `d = (t+1)*(ell-1)` and
`m = psi(n) = if n <= t then n else t + ell*(n-t)`.
The elementary helper `trace_indices` proves, for `t <= n` and `ell > 0`,

- `(d + m) / ell = n`,
- `(d + m + 1) / ell = n + 1`.

It first writes `m = t + ell*(n-t)`, including the equality case `n=t`,
then proves the lower and strict upper inequalities characterizing each natural
quotient. No ramification theorem is used in this arithmetic helper.

`trace_bound` extracts the forward implication of the supplied exact trace-image
proposition and uses monotonicity of ideal powers to weaken the target bound.
`trace_coefficient_of_arithmetic` applies that bound to the integral source
uniformizer power and constructs its `dividedTrace`. The resulting integer has
field value exactly `Tr(piL^m)/piF^n`. The reverse implication of the trace-image
proposition supplies surjectivity onto the nth target ideal power. Together
with the next-power bound, the imported `trace_coefficient_ne_zero` proves
nonvanishing of the coefficient's residue: a trace preimage of `piF^n` gives,
after integral division and reduction, a product equal to one. This argument
uses exact trace surjectivity rather than a zero-sensitive order convention.

`critical_of_arithmetic` handles `0 < t` with source and target index `t`.
It obtains the literal nonzero norm coefficient `N(piL)^t/piF^t` from
`norm_coefficient` and the literal nonzero trace coefficient
`Tr(piL^t)/piF^t` from the preceding helper. For an arbitrary source unit,
put `delta=x-1` in the tth source ideal power. The supplied norm-expansion
proposition gives a remainder `Tr(z)` with `z` in the `(2*t)`th power.
Since `2*t >= t+1`, the trace-image bound puts this remainder in the
`(t+1)`st target power. Its quotient by `piF^t` has zero residue.
`coordinate_of_expansion` therefore leaves just the trace and norm terms.
`trace_term_coordinate` computes the linear trace term;
`norm_term_coordinate` computes the norm term with exponent `ell`.
The imported positive-break theorem identifies `ell=p`, and commutativity
of addition puts these terms in the target's order: norm term followed by trace.

`above_of_arithmetic` handles `t < n`, including the tame case `t=0`.
Primality gives `ell >= 2`, hence `m >= n+1` and `m > 0`.
The trace coefficient is again the exact nonzero quotient
`Tr(piL^m)/piF^n`. The norm of `delta=x-1` lies in the mth target ideal
power and thus in its `(n+1)`st power. The expansion remainder starts in
source power `2*m`; since `2*m >= m+1`, its trace also lies in target
power `n+1`. Both divided residues vanish. Dividing the actual expansion
therefore leaves precisely the linear trace term computed by
`trace_term_coordinate`, at source index `psi(n)` and target index `n`.

Finally `primeGradedNormFromArithmetic` introduces the two arithmetic proofs
and every quantifier of the full target. It combines the imported
`residue_bijective`, both `filtration_containments_of_arithmetic`, and
`zero_coordinate` with the imported `below_break_of_arithmetic` and the two
new coordinate cases. The zero-level and both full-index containment clauses
are included without a positive-index restriction; the critical formula alone
requires a positive break, exactly as in the target. Each coordinate formula
holds for every source and target filtration representative related by the
actual unit norm. No arbitrary replacement for a literal coefficient occurs.

The provenance is an internal assembly of the imported support lemmas and the
two explicit arithmetic inputs. The mathematical calculation is Serre,
*Local Fields* (1979), V.3, Propositions 4–5 and the proof of Proposition 5,
printed pages 84–85 (PDF pages 91–92). The implemented proof uses trace
surjectivity to show nonvanishing at the critical index, while Serre uses the
ramification kernel there. The registered 2019 author corrections, PDF pages
2–3, contain no correction to this passage.

The final theorem explicitly binds its universes in the order `u, v`, matching
the published statement and preserving the two independent field universes.
