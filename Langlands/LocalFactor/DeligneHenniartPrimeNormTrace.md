# Norm and trace above a prime ramification break

Worker 126 authored this internal arithmetic step toward DH81 Corollary
3.12(i). It does not prove the full `TopLayerNormTraceStatement`.

`PrimeNormTraceIdealBoundsStatement` states the bounds below, and
`prime_normTrace_ideal_bounds` proves them. This proposition applies to a prime-degree totally
ramified Galois extension `L/K` of p-adic fields, in independent universes.
The proposition explicitly binds its finite-dimensional and Galois instances,
and the theorem has exactly this named proposition as its type. It therefore
retains those hypotheses even though its ideal-bound formula does not mention
the instances directly.
The supplied natural break `t` must describe every lower ramification group:
the group is full through `t` and trivial afterward. For each natural `n > t`,
put `ell = [L:K]` and `m = t + ell * (n - t)`. For every element `x` of the
`m`th maximal-ideal power in the canonical integer ring of `L`, the theorem
provides actual integral representatives of its trace in the `n`th
maximal-ideal power of `K`, and of

```
N(1 + x) - 1 - Tr(x)
```

in the `(n + 1)`st power. Membership is sufficient; exact valuation and
nonzeroness are not required. The relative degree may be any prime,
including a prime different from the residue characteristic when `t = 0`.

The proof imports the published exact trace-ideal formula and prime norm
expansion. The trace indices are `n` for depth `m`, and `n + 1` for depth
`m + 1`. Since `m >= n + 1` and `2m >= m + 1`, the expansion

```
N(1 + x) - 1 - Tr(x) = N(x) + Tr(z),    z in maximalIdeal^(2m),
```

has both right-hand terms in the `(n + 1)`st power. The norm term uses the
published order formula for a totally ramified extension. Their sum is the
explicit integral representative of the remainder.

This is a derived assembly of `primeRamifiedTraceIdeals`,
`primeNormTraceExpansion`, `PrimeGradedNorm.trace_indices`,
`PrimeGradedNorm.trace_bound` and `PrimeGradedNorm.integerNorm_mem_pow`.
The arithmetic inputs formalize Serre, *Local Fields*, V section 3,
Lemmas 4–5 and the above-break case of Proposition 5. The argument supplies
the prime totally ramified case used in the reductions of Deligne–Henniart,
*Sur la variation, par torsion, des constantes locales d'equations
fonctionnelles de fonctions L* (1981), sections 3.9–3.12, printed pp.106–107.
The original DH81 passage was read in the registered source
`deligne-henniart-1981-variation`, PDF pp.18–19. This module uses the
published arithmetic results by import; it copies no original-source Lean
code and makes no claim about the remaining tower or tame-base-change steps.
