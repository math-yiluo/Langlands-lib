# Rational equal-rank zeta transport under additive-character change

This is internal derived content. It specializes the published character-change
integral identity in `RankinSelberg.CharacterChange` using the Laurent-unit and
rational-continuation API in `RankinSelberg.LaurentTransport`. It reuses the
intrinsic coefficient sets, rational zeta values and normalized polynomial
generators of `RankinSelberg.LocalFactor`. The p-adic specialization uses
`normalizedAbsoluteValue` from `RankinSelberg.AnalyticStatement` and the proved
normalization laws in `LocalField.Normalization.Proof`. No independent external
source assertion is introduced.

## Definitions and assumptions

For a field `F`, an absolute value `abv : AbsoluteValue F ℝ`, a unit `a`, and a
natural `n`, let `d_a = characterChangeElement a n`, whose diagonal entries are
`a^n, a^(n-1), ..., 1`. The imported positive-root quotient modulus is
`c = characterChangeModulus abv a n = |a|^(sum_{i<j}(j-i))` for indices in
`Fin (n+1)`. `characterChangeScalar` packages its nonzero complex image as a
complex unit. For an integer `k`, `characterChangeLaurentUnit` is the actual
Laurent unit `C(c) T(-k)`, with rational image `C(c) X^(-k)`. Its definition
makes sense for every integer; its role as the integral multiplier requires the
normalization below.

The general transport results assume a topological field with
`IsTopologicalRing F`, an additive unitary character `ψ`, a Borel measurable
structure on the actual quotient `N_(n+1) \ GL_(n+1)`, a measure `μ`, a positive
natural `q`, an integer `k`, and both explicit laws:

- `HasCharacterChangeMeasureLaw abv a μ`, namely
  `map(characterChangeQuotient a n, μ) = c • μ`;
- `abv (det d_a) = (q : ℝ)^(-k)`.

The measure law is an assumption here. This module does not prove that the
canonical compatible quotient Haar measure satisfies it. The theorems also
allow the zero measure. Neither irreducibility, genericity, smoothness, nor
admissibility is needed for this conditional transport of actual coefficient
sets. Representations are over arbitrary complex modules.

## Implemented integral and continuation arguments

`determinantWeight_eq_spectralPoint_zpow` proves `|det g|^s = X(s)^k` whenever
`|det g| = q^(-k)`, with `X(s) = q^(-s)`. The proof uses the complex integer-power
identities and the zero argument of the positive real base `q`; the branch
conditions are checked explicitly.

The imported integral identity is `D(s) I_new(s) = c I_old(s)`, where
`D(s) = |det d_a|^s`. Dividing by its nonzero determinant weight and substituting
the spectral power gives

`I_new(s) = c X(s)^(-k) I_old(s)`.

Multiplying the same identity by `c^(-1)` gives the reciprocal formula

`I_old(s) = c^(-1) X(s)^k I_new(s)`.

These are identities of the total scalar Bochner integrals for every complex
`s`. The transformed functions are exactly `characterChangeFunction` and
`characterChangeInverseFunction`; the Schwartz–Bruhat function `Φ` is unchanged
because the last row of `d_a g` is the last row of `g`. The reciprocal formula
uses the same measure law, with no additional inverse-character measure law.

`equalRankContinuation_characterChange` and its reverse apply
`HasRationalContinuation.monomial_mul` to these pointwise identities. Thus a
rational continuation `R` is sent to `C(c) X^(-k) R`, and a continuation of the
transformed integral is sent back to `C(c^(-1)) X^k R`. The imported continuation
relation includes denominator nonvanishing on a right half-plane; the Laurent
transport lemma handles it, including negative powers.

## Actual zeta witnesses and normalized generators

The forward zeta-value theorem unpacks the coefficient functions, the test
function, half-plane convergence, and rational continuation in a zeta-value
witness. It transports both coefficient functions using the published image
identities for `whittakerSet` and `inverseWhittakerSet`, transfers convergence
with `equalRankConverges_characterChange_iff`, and applies the forward
continuation formula.

The reverse theorem first uses those exact image identities to recover original
coefficient functions from arbitrary coefficients for `ψ.scale a`. It then
transfers convergence and continuation back. Consequently both reciprocal
Laurent-unit transports apply to the full intrinsic sets of actual rational
zeta values, without choosing a Whittaker functional or assuming uniqueness of
models.

`zetaSpan_equalRank_characterChange` applies the proved monomial-unit span
criterion to these two membership maps. `isEqualRankLPolynomial_characterChange`
then transports the normalized-generator relation through equality of the
actual Laurent spans. `normalizedGeneratorExists_equalRank_characterChange`
transports the imported existence-and-uniqueness predicate in both directions.
None of these results establishes existence in either character independently.

## P-adic specialization and scope

For a specified p-adic extension `K` with topological data `T`,
`normalizedDeterminantWeight_eq_spectralPoint_zpow` sets
`q = T.residueCardinality` and `k = T.ord (det g)`. It discharges the numerical
hypothesis using `T.normalizedAbs_of_ne_zero` and the determinant's nonzeroness;
`T.residueCardinality_gt_one` supplies positivity of `q`.

`zetaSpan_equalRank_characterChange_normalized` and
`isEqualRankLPolynomial_characterChange_normalized` install the topology from
`T` and the Borel quotient structure. They specialize to the published
residue-cardinality absolute value and discharge the determinant normalization
internally. They still explicitly require the character-change measure law for
`μ`. The remaining canonical Haar modulus theorem is a separate obligation.
No unequal-rank transport, analytic existence theorem, functional equation,
epsilon-factor formula, or conductor identity is claimed here.
