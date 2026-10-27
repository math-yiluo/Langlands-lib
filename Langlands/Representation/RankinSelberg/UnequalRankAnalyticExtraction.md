# Actual unequal-rank continuations from analytic inputs

This module selects rational continuations from an explicitly supplied
`UnequalRankAnalyticAt` premise. It proves that the selected family contains a
nonzero value when q > 1, and combines the original and dual analytic inputs
with the published conditional comparison to produce the exact fixed-data
block-zero gamma conclusion.

This is a derived adapter. The analytic conclusions, continued covariant
forms and full fixed-data uniqueness remain explicit hypotheses. The module
does not prove the universal analytic, continued-forms, uniqueness or
block-zero gamma existence statements.

## Data and selected continuations

The generic block lemmas use a field F in universe uF, its supplied topology
and measurable space, natural numbers n,r,j,k, and an equality
hr : r = n+(j+k+1). The rectangular space has its induced product measurable
structure, and the actual left-unipotent quotient has its supplied measurable
space. Representation carriers V and W are complex modules in independent
universes uV and uW. The representations pi and sigma have ranks r+1 and
n+1. Their specified functionals ell and ell' use the standard and inverse
standard characters of the supplied unitary additive character psi.

Fix q, an absolute value abv, a quotient measure mu and a measure nu on the
j-by-(n+1) rectangular space. An input

```text
hA : UnequalRankAnalyticAt j k hr q psi abv mu nu pi sigma ell ell'
```

already asserts all four analytic clauses for this actual family.
`UnequalRankAnalyticAt.exists_continuation` extracts its second clause. The
proof substitutes only the natural-number rank equality and obtains, at every
pair f,f' in the actual coefficient-image submodules, a rational function
continuing

```text
unequalRankIntegralAt j k hr psi abv mu nu f.val f'.val.
```

`UnequalRankAnalyticAt.continuation hA f f'` chooses such a function using
classical choice. `continuation_spec` is its defining property. The definition
is conditional on hA; it supplies no analytic existence theorem independently
of that input.

## A nonzero selected value

`UnequalRankAnalyticAt.exists_ne_zero` extracts normalized-generator existence
from hA's fourth clause and applies the published
`IsNormalizedGenerator.exists_ne_zero`. Its conclusion is a nonzero member
of the exact `unequalRankValuesAt` set. No irreducibility or nonzero
functional premise is added to this conditional extraction.

For q > 1, `exists_continuation_ne_zero` transfers that witness to the selected
family. It unfolds value-set membership with `unequalRankValuesAt_eq_set`,
obtaining a vector pair and a nonzero continuation for its actual integral.
The selected continuation has the same integral and therefore equals this
witness by `HasRationalContinuation.unique`. Thus

```text
exists f f', hA.continuation f f' != 0.
```

This argument uses uniqueness of continuation on a common right half-plane.
It does not require a nonzero evaluation at any particular spectral parameter.

## Fixed-data block-zero assembly

`exists_blockZeroGammaEquation_of_analytic` assumes a topological ring
structure on F, a supplied additive Haar measure nu, and n < r. Set
k = r-n-1. Its remaining hypotheses are precisely:

- q > 1;
- sigma is of Whittaker type for the inverse standard character;
- the original `UnequalRankAnalyticAt` conclusion for block (0,k), using mu
  and `rectangularMeasure nu 0 (n+1)`;
- the inverse-transpose analytic conclusion for block (k,0), using the inverse
  character psi.scale(-1), the same mu and nu, and the actual
  `firstDualFunctional` and `secondDualFunctional`;
- `UnequalRankBlockZeroContinuedFormsConclusion` for the original data;
- `UnequalRankBilinearUniquenessConclusion` for the original data.

The original rational family R is the continuation selected from the first
analytic input. The dual family Rd is selected from the second analytic input
after applying `translatedFirstDualModelEquiv` with
`blockWeylAt n r hnr` to the first original coefficient vector and
`secondDualModelMap` to the second. The values of these maps give exactly the
functions in `dualUnequalRankModelIntegralAt`, including the complementary
rectangular block, inverse character and actual Weyl right translation.
Consequently the selected dual function continues that published integral,
with its unreflected parameter. No smooth-contragredient identification is
assumed.

The generic nonzero-value lemma gives a nonzero original selected value and
separately a nonzero value on the dual coefficient models. Surjectivity of the
actual translated first-model equivalence and second-model map supplies
original-model preimages of the latter witness. Hence Rd has a nonzero value
as a family on the original vector pairs. The original and dual witnesses
may have different indices.

The proof constructs the complex unit delta with value q^(-1), derives the
actual minus-one scalar from sigma's Whittaker-type hypothesis using
`modelMinusOneScalar` and
`hasModelMinusOneScalar_modelMinusOneScalar`, and applies the published
`UnequalRankBlockZeroContinuedFormsConclusion.exists_gammaEquation`.
The result is exactly

```text
exists G : RationalFunctions, G != 0 and
  UnequalRankBlockZeroGammaEquation hnr q psi abv mu nu pi sigma ell ell' G.
```

The existing comparison theorem retains exponent r and the three
reduced-denominator conditions in `GammaFunctionalEquation`. The new adapter
does not alter the integrals, quotient measure, scalar Haar measure or gamma
domain, and does not assert across-block generator equality. It derives the
continuation choices, separate nonzero witnesses and minus-one scalar from
the listed inputs. The analytic, covariance and uniqueness premises still
have to be discharged to prove the universal p-adic target.

## Provenance

This module is internal derived content using the published
`UnequalRankAnalyticAt` interface in `UnequalRankGammaFactor`, continuation
uniqueness in `RationalContinuation`, normalized-generator nonvanishing in
`EpsilonFactor`, the actual coefficient-model maps and value-set identity
in `DualModels`, and the conditional assembly in
`UnequalRankBilinearComparison` and `ModelMinusOneScalar`. It makes no new
claim from original literature and uses none of the unresolved universal
proof targets as theorems. Imported Lean/Markdown pairs are unchanged.

Worker 112 implemented this adapter. Published dependencies retain their
authorship; no unpublished peer draft is incorporated here.
