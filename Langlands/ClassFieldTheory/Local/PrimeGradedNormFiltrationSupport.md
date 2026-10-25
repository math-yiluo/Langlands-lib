# Integer-unit norms and conditional filtration transport

Worker 96 authored this internal assembly module. It bundles the actual integral
norm as `integerNormHom` and its map on integer-ring units as `integerUnitsNorm`.
Both retain the arbitrary independent universes, supplied field algebra,
compatible Padic scalar tower and finite-dimensionality assumptions of the
underlying construction. They do not require Galoisness or total ramification.

`integerUnitsNorm_inclusion` identifies the inclusion of this integer-unit norm
into field units with the existing determinant `normUnits`. Recovering the
integer unit underlying a source filtration element proves
`norm_mem_filtration_iff`: its field norm is in the target nth filtration group
exactly when its integer norm minus one is in the nth power of the target
maximal ideal. `norm_mem_filtration_zero` follows because the zeroth ideal power
is the entire integer ring. It applies to a source element at any level.

`norm_mem_filtration_of_expansion` is an elementary conditional implication.
For a source unit `x` at level m and n <= m, it assumes an actual field equality

```text
N(x) - 1 - Tr(x-1) - N(x-1) = Tr(z)
```

and integers `a,b` in the target nth ideal power whose exact field values are
`Tr(x-1)` and `Tr(z)`. The source integer `x-1` lies in the mth ideal power.
Under the explicit total-ramification identity, the previously proved norm
ideal-power containment puts `N(x-1)` in the nth target ideal power. The
expansion equality identifies the target integer norm minus one with
`a + integerNorm(x-1) + b`. Closure under addition proves the claimed unit
filtration containment.

The next lemma, `norm_mem_filtration_of_arithmetic`, explicitly takes proofs of
`PrimeRamifiedTraceIdeals.{u,v}` and `PrimeNormTraceExpansion.{u,v}` as parameters.
It does not supply either proof. With prime actual degree ell, total
ramification, Galoisness and the supplied actual lower-group break pattern, it
uses those parameters to obtain the required integers `a,b` and actual remainder
`z`. If `n <= m` and `n <= ((t+1)*(ell-1)+m)/ell`, the trace formula bounds the
first trace term. The remainder lies in the source power 2*m, so monotonicity
of natural division bounds its trace by at least the same target level. The
previous elementary implication then gives norm containment.

`graded_index_bounds` is a pure natural-number lemma valid for every positive
ell and every t,n. For

```text
m = if n <= t then n else t + ell*(n-t),
d = (t+1)*(ell-1),
```

it proves `n <= m`, `n <= (d+m)/ell` and `n+1 <= (d+m+1)/ell`. The proof splits
at `n <= t`, converts each floor-division inequality to multiplication using
ell > 0, and checks the resulting integer polynomial inequalities. It includes
n=0 and t=0.

`filtration_containments_of_arithmetic` applies these bounds to obtain both
requested containments, at source levels m and m+1. This theorem still has the
two arithmetic propositions as explicit proof parameters. It is a checked
assembly implication, not an unconditional proof of either containment or of
`PrimeRamifiedGradedNorm`. The exact task cannot be completed until genuine
published proofs discharge these parameters and the remaining positive
coordinate formulas are proved.

These constructions and implications are internal assembly of the imported
integer-unit, norm-order and ideal-coordinate results. Their arithmetic pattern
is the deduction of Proposition 4 from Lemmas 4–5 in Jean-Pierre Serre,
*Local Fields*, V.3, printed pp.83–84 / PDF pp.90–91, registered as
`serre-1979-local-fields`. Worker 96 read V.3, printed pp.83–85 / PDF pp.90–92
and the registered 2019 author corrections, PDF pp.2–3; no correction affects
this passage. No different/trace arithmetic, orbit-expansion arithmetic or
positive graded-coordinate conclusion is claimed by this support module.
