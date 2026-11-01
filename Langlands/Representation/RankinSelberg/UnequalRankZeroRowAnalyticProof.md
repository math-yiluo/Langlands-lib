# Zero-row unequal-rank convergence, rationality and a uniform denominator

Worker 331, with contributions from Workers 329 and 64.

The theorem `Langlands.RankinSelberg.unequalRankZeroRowAnalytic` proves exactly
`UnequalRankZeroRowAnalyticStatement.{uF,uV,uW} F T n k`. For every prime,
p-adic field `F`, supplied topological data `T`, and natural numbers `n,k`,
it gives absolute convergence on a right half-plane for each actual coefficient
pair, rational continuation of its actual nested integral, and one nonzero
Laurent denominator clearing the entire rational-value set at the fixed data.
The theorem has no additional analytic premises.

The larger and smaller ranks are `n + (0 + k + 1) + 1` and `n + 1`.
The positive gap is `k + 1`, and the determinant exponent is
`s - (k + 1)/2`. The independent field and representation universes, arbitrary
supplied topology, full Whittaker-type hypotheses (including reducible
representations), nonzero functionals, actual coefficient images, compatible
quotient measure and arbitrary additive Haar measure are those of the
unchanged target. Both `n = 0` and `k = 0` are included.
The right-half-plane bound may depend on the coefficient pair.

## Torus expansions and compact averaging

The private assembly routine first applies `modelAsymptoticTransfer` to
`Langlands.whittakerTypeAsymptotic`, separately at universes `uV` and `uW`.
This gives full-torus expansions for the actual coefficient images in the
supplied topology, with the standard and inverse Whittaker characters.
The imported theorem applies to the full admissible, finitely generated
Whittaker-type scope; it imposes neither irreducibility nor a unitary central
character.

The published `unequalRankZeroRowRootExpansion` then chooses a finite family
`η : Fin m → A → ℂ`, where `A = Fin (n + 1) → F.Carrierˣ`.
Each member is continuous with finite-dimensional left-translation span.
This family is chosen from the representations before the functionals,
coefficient pairs or compact representatives vary. In root coordinates
`d(a)_i = ∏_{j ≥ i} a_j`, set

```text
w(a) = (∏ᵢ |aᵢ|^((i+1)(n-i)))⁻¹,
v(a,s) = ∏ᵢ |aᵢ|^((i+1)s).
```

Here the absolute value is the normalized one supplied by `T`, and the
powers in the Lean formulas are complex powers of the nonzero positive
absolute values. The fixed determinant shift `-(k + 1)/2` and the inverse
Borel modulus are incorporated into the root expansion's finite functions.
For each coefficient pair and representative in the integral compact subgroup,
the weighted integrand is a sum
`∑ j, Ψ_j(coe a) * η_j(a) * v(a,s)` with genuine Schwartz–Bruhat functions
`Ψ_j` on the full root-coordinate field space.

For each coefficient pair, `unequalRankZeroRowNormalizedCompactIntegration`
provides finitely many representatives and nonnegative real weights for the
restricted ambient general-linear Haar measure on that compact subgroup.
The representatives and weights are independent of `a` and `s`.
It supplies compact integrability and both the complex integral and extended
norm averaging formulas. Substituting the root expansion at those
representatives and applying `weighted_compact_formulas` gives the same
formulas after multiplication by `w(a)`. This private calculation uses
linearity of the integrable compact integral, multiplicativity of the
extended norm, and finiteness of the norm of a complex scalar.

## Mellin analysis and the common denominator

`root_analytic_of_finite_formulas` applies the published
`finiteFunctionMellin` to the fixed finite set `Finset.univ.image η`,
with the positive spectral multiplicities `i.val + 1`.
It obtains a single nonzero Laurent polynomial `D` clearing all resulting
Mellin rational functions for every member of that set and every
Schwartz–Bruhat test.

For a fixed coefficient pair, the compact formula has only finitely many
Mellin summands. A finite upper bound on their convergence bounds makes all
summands integrable on a common right half-plane. Finite-sum integration
then proves integrability of the compact average and finiteness of its
iterated extended norm integral. In particular, noncompact complex
finite-sum identities are used only in that half-plane, after integrability
has been established.

The average has a rational continuation given by a finite constant linear
combination of the Mellin continuations, using
`RationalContinuationLinear.continuation_sum`,
`continuation_linear_combination` and `continuation_of_eq_on_right`.
This rational function belongs to the Laurent span of the fixed Mellin
rational-value set. `denominator_clears_span` therefore keeps the same `D`
for every coefficient pair. If any other rational function is a continuation
of the same average, uniqueness of rational continuation, using
`T.residueCardinality_gt_one`, identifies it with the constructed one.
Thus `D` clears all continuations in the target set, rather than merely
one chosen continuation for each pair.

The changing compact representatives, averaging weights and Schwartz
functions do not change the finite `η` family or the denominator supplied
for all its Schwartz tests. This is the uniformity needed by the third
conclusion. Empty finite families and zero coefficients require no separate
nonvanishing assumption.

## Quotient integration and the zero-row measure

`analytic_of_root_average` supplies the published
`quotientIwasawaIntegration F T n` to `quotientRootIntegration`.
Measurability of the quotient integrand follows from
`unequalRankZeroRowIntegrandContinuous`, applied in the supplied topology.
Continuity of its normalized absolute value is
`NNReal.continuous_coe.comp T.continuous_normalizedAbsHom`.

The root-coordinate formula first identifies quotient integrability with
finiteness of the iterated extended norm integral. The preceding Mellin
bound therefore establishes quotient integrability. Only then does the
proof use the complex Iwasawa integral identity to identify the quotient
integral with its compact root average. The equality uses the actual Haar
normalizations and every compatible quotient measure, with scalar one.

The two private lemmas `zero_row_converges_iff` and `zero_row_integral_eq`
use `rectangularMeasure_zero_rows`: the actual zero-row rectangular product
measure is the Dirac measure at the unique matrix. Integrating out this
probability factor gives one direction of the integrability equivalence.
The converse uses the product with the integrable constant one. The actual
nested integral reduces by `integral_dirac`. No extra sigma-finiteness
assumption on the supplied quotient measure is needed.

Equality on a right half-plane transports rational continuations between
the root average and the actual model integral. Applying this equality in
both directions retains the specified `D` for every member of
`unequalRankRationalValues`. The final theorem supplies the two published
full-torus instances and the published Mellin theorem to the private
assembly, leaving exactly the target's field, topology and rank binders.

## Sources and contribution provenance

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The relevant original pages are Section 2.5, pp.388–389, Theorem 2.7(i)–(ii),
pp.390–391, and its proof, pp.391–394. These are zero-based PDF pages 22–28.
Display (7) on p.394 has the diagonal restriction and the full gap-dependent
determinant exponent used here. The following paragraph applies the preceding
torus argument to obtain convergence and rational functions with a fixed
denominator. On pp.391–392 the finite families depend on the representations,
while the Schwartz data vary with the coefficients.

The implementation assembles the published full-torus, coefficient-model,
root-expansion, compact-integration, finite-function Mellin, continuity and
Iwasawa proofs by their Lean names. Its private finite-sum and transport
arguments are derived from the Library's integral and continuation definitions;
they are not additional assertions attributed verbatim to JPSS.
The zero-row Dirac lemmas reuse Worker 329's shared reduction draft for
task `b01bbdd0-5321-41f4-908e-2048e837da34`.
The weighted compact calculation and finite-Mellin assembly adapt Worker 64's
`CompactRootExpansionProof` and `RootAverageAnalyticProof`, respectively.
Those contributions account for the recorded coauthors.

This theorem proves the three analytic conclusions only.
Normalized-generator existence and unit-span membership are separate targets.
