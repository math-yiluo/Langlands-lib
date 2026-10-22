# Change of additive character: quotient transport

Worker 43 derives this interface from the published modules
`Whittaker/CharacterChange`, `RankinSelberg/QuotientIntegrals`,
`RankinSelberg/LocalFactor`, and `Analysis/Local/QuotientMeasure`.
It introduces no new source convention. The matrix, the scaled additive
character, Whittaker functionals, coefficient models and scalar integrals
are those modules' actual constructions. This is internal derived content;
it does not claim that the analytic measure-scaling obligation below has
been proved from the local-field Haar constructions.

Throughout, `F` is a field with a ring topology, `a : Fˣ`, and rank is
`r = n + 1`. There is no topology on the representation's vector space.

## Quotient translation

Write `d_a = diag(a^n, a^(n-1), ..., 1)`, the published
`Whittaker.characterChangeElement a n`. Conjugation by `d_a` preserves the
upper-unipotent subgroup `N_r`. The forward implication of
`characterChange_mem_unipotent_iff` is the published conjugation map for
`a⁻¹`, followed by cancellation; the reverse implication uses the map for
`a`. This supplies the equivalence of coset relations needed by Mathlib's
`Homeomorph.Quotient.congr`.

`characterChangeQuotient a n` is therefore the actual homeomorphism
`T_a : N_r \ GL_r(F) → N_r \ GL_r(F)`, `N_r g ↦ N_r d_a g`.
Its representative formula is proved by reflexivity, and
`characterChangeQuotient_inv` identifies its inverse with `T_(a⁻¹)`.
The quotient carries the existing quotient topology, and all measure
results require its measurable structure to be Borel.

## The explicit measure obligation

`characterChangeRootExponent n` is the natural number
`E = sum_{0 ≤ i < j < r} (j-i)`. No closed formula for this finite sum is
needed or asserted. For a supplied real-valued absolute value `abv`,
`characterChangeModulus abv a n` is the nonnegative real number
`c = abv(a)^E`. Its nonzeroness follows from `a` being a unit.

`HasCharacterChangeMeasureLaw abv a μ` is the proposition

```
Measure.map T_a μ = (c : ℝ≥0∞) • μ.
```

This is a concrete property of the supplied quotient measure, rather than
an assertion about every measure. It also imposes no nonzeroness or Haar
condition on `μ`; those belong to the eventual construction theorem. In
particular it is satisfiable by the zero measure. The intended nonzero
local-field instance must use the normalized absolute value and a quotient
measure compatible with the published group and unipotent Haar measures.

The sign of the proposed factor can be checked by the Weil integral formula:
conjugation `u ↦ d_a u d_a⁻¹` scales the `(i,j)` root coordinate by
`a^(j-i)`. If its pushforward on unipotent Haar measure is `c⁻¹` times that
measure, then averaging `g ↦ f(d_a g)` is `c⁻¹` times the average of `f` at
`T_a(N_r g)`. Left invariance of the ambient group measure consequently
requires the quotient pushforward to be `c` times the quotient measure.
This paragraph motivates the obligation; neither the unipotent Jacobian
nor its deduction from compatibility is proved in this module.

Given this explicit law, `integral_characterChangeQuotient` proves
`∫ f(T_a q) dμ = c • ∫ f(q) dμ` for every complex-valued function. The proof
uses the measurable equivalence's change-of-variables theorem and the
scalar-measure integral formula; these are total Bochner integrals.
`integrable_characterChangeQuotient_iff` separately proves that composition
with `T_a` preserves integrability, using finiteness and nonzeroness of `c`.
No convergence is inferred merely from an integral identity.

## Whittaker sets and equal-rank integrals

`whittakerSet_characterChange` and `inverseWhittakerSet_characterChange`
identify the intrinsic coefficient sets for `ψ.scale a` with the images
of those for `ψ` under the published left-translation maps. The proofs
write a coefficient as a functional applied to a represented vector,
use surjectivity of the published functional equivalence, and apply its
coefficient formula. They need no multiplicity-one, smoothness, genericity,
or irreducibility hypothesis.

The last diagonal entry of `d_a` is one, so
`lastRow_characterChangeElement_mul` proves `lastRow(d_a g) = lastRow(g)`.
`determinantWeight_mul` proves the multiplicativity of `|det g|^s`, using
multiplicativity of determinant and absolute value and the complex-power
formula for nonnegative real factors. `determinantWeight_ne_zero` uses
invertibility of the matrix and the nonzero-base property of complex power.

Put `D(s) = determinantWeight abv d_a s`, `W_a(g) = W(d_a g)` and
`W'_a(g) = W'(d_a g)`. The representative calculation descends to
`equalRankIntegrand_characterChange`:

```
integrand(ψ, W, W', Φ, s)(T_a q)
  = D(s) * integrand(ψ.scale a, W_a, W'_a, Φ, s)(q).
```

The Schwartz–Bruhat test `Φ` stays unchanged. Combining this identity with
the explicit measure law gives `equalRankIntegral_characterChange`:

```
D(s) * integral(ψ.scale a, W_a, W'_a, Φ, s)
  = c • integral(ψ, W, W', Φ, s).
```

Finally, `equalRankConverges_characterChange_iff` proves equivalence of the
two integrability predicates, using the quotient integrability result and
`D(s) ≠ 0`. These are conditional identities for the supplied measures,
not unconditional invariance of rational zeta values or normalized
L-polynomials. Turning `c / D(s)` into a Laurent unit under local-field
normalization, transporting rational continuations, and the unequal-rank
block calculation remain separate work.
