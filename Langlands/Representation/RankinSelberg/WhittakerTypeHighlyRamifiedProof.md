# Highly ramified L-vanishing for Whittaker-type pairs

Authors: Worker 394 and Worker 331.

`Langlands.RankinSelberg.whittakerTypeHighlyRamifiedLVanishing.{uF,uV,uW}`
proves exactly
[WhittakerTypeHighlyRamifiedLVanishingStatement](WhittakerTypeHighlyRamifiedStatement.md).
It has no additional premises. For every pair of representations of full
Whittaker type, it chooses a natural threshold before every continuous
quasicharacter. Above that threshold, the determinant twist of the first
representation has symmetric L-polynomial `1` against the second.

The theorem retains reducible representations, all positive ranks in both
orders, independent field and representation universes, any nontrivial unitary
additive character, and the supplied self-dual Haar measure. The threshold is
uniform over arbitrary unramified parts. Its conclusion is the complete
`IsPadicSymmetricLPolynomial` relation: compatible-measure existence and every
compatible quotient measure, including every unequal-rank block.

## Fixed finite functions and the conductor threshold

The published [full-torus Whittaker asymptotic theorem](../Whittaker/TypeAsymptoticProof.md)
and [model transfer](ModelAsymptoticProof.md) supply coefficient torus
expansions for the two representations. The same-representation equivalence
`isOfWhittakerType_standard_iff_inverse` supplies both character signs.
The asymptotic theorem is instantiated separately at `.{uF,uV}` and
`.{uF,uW}`, with no equality of the carrier universes. Its finite family is
chosen before the functional, vector, and twisting character, including the
unrestricted central coordinate.

`exists_equalRankRootExpansion_twist` applies the published equal-rank root
expansion to untwisted coefficient models. The Whittaker-set twist equivalence
then expresses each twisted function as an untwisted function times its
character multiplier. `determinantCharacter_rootCoordinates` identifies the
multiplier at a cumulative-product diagonal times a right translate as

```text
(product_i chi(a_i)^(i.val+1)) * chi(det(k)).
```

Unit extensionality lifts the published field-valued root-coordinate
determinant identity to units. The determinant and character homomorphisms
preserve the products. The right-translate multiplier is absorbed into the
Schwartz coefficients, retaining the original finite family before `chi`.
The unequal-rank adapter uses the published zero-row root expansion and the
identity for the determinant of `unequalRankMatrix`. The spectral shift
`s - (k+1)/2` remains in that expansion's fixed finite family.

`exists_uniform_ramified_tensor_integrals` first selects a scalar
principal-unit level for each of finitely many one-variable factors. The
published [positive-power conductor theorem](../../HarmonicAnalysis/PrincipalUnitPowerCofinalityProof.md)
gives a conductor threshold making each character power nontrivial on its
selected level. A natural upper bound for these finitely many thresholds is
chosen before the quasicharacter and every Schwartz test. This includes all
positive weights, even weights divisible by the residue characteristic; the
proof does not equate the conductors of a character and its powers.

`exists_uniform_ramified_finiteFamily_integrals` supplies these scalar inputs
from the published [finite-function tensor theorem](FiniteFunctionTensorProof.md)
and [ramified finite-function Mellin theorem](RamifiedFiniteFunctionMellinProof.md).
For each member of the fixed family, it selects its finite tensor expansion
before the character, obtains a bound independent of every test, and takes a
further finite upper bound. A Schwartz test's tensor expansion is selected
only after this bound. The root specialization
`exists_uniform_ramified_root_integrals` uses weights `i.val+1` and the
published [row tensor decomposition](../../HarmonicAnalysis/RowTensorDecompositionProof.md)
to discharge its Schwartz tensor premise. Hausdorffness and the canonical
nonarchimedean topology provide the required topological instances.

The generic tensor helper has explicit scalar-certificate hypotheses for
arbitrary functions. The finite-family and root specializations discharge
them by the published theorems. Their resulting bound precedes the character,
family member and test, so varying the unramified part never changes the
chosen bound.

## Actual integrals and Laurent continuation

`hasRationalContinuation_finset_prod` proves continuation for finite products,
including the empty product, using multiplicativity and the Laurent algebra
map. `laurentContinuation_product_integral` takes a common bound for the
finitely many convergence thresholds and applies finite Fubini to actual
product-measure integrals. The sum helper similarly uses a common right
half-plane to interchange a finite sum and the integral. Its Laurent
coefficient is `sum_i C(c_i) * L_i`. The tensor helper distributes both finite
expansions and applies the product and sum results. Sigma-finiteness of the
normalized multiplicative Haar measures follows from the supplied field's
Hausdorff and second-countability properties and the units embedding.
No claim of convergence outside the resulting half-plane is needed.

The compact adapters apply the published normalized mass-one compact
integration theorems. Openness of the character kernel makes each continuous
determinant twist smooth. The finite compact representatives, weights and
Schwartz coefficients may depend on the character and input functions;
the finite-function family remains fixed. The root spectral-weight identity
inserts the same positive exponents. Factoring the inverse-modulus weight
out of the compact integral gives exact finite-sum formulas for both the
ordinary integral and its extended-norm integral.

The equal-rank and zero-row quotient adapters use the uniform ramified torus
certificates to prove a common convergence half-plane and Laurent continuation
for the compact average. Its exact norm formula proves finiteness of the
iterated absolute integral on that half-plane. The published continuity
proofs make the actual quotient integrand measurable. Only then does the
published root-integration transport identify its convergent integral with
the compact root average. Uniqueness of rational continuation identifies each
zeta value with its Laurent representative. The unequal zero-row rectangular
measure reduces the inner integral to a Dirac evaluation. Its conclusion
allows every supplied additive Haar measure.

The quotient Iwasawa premise of the reusable adapters is discharged in the
final assembly by the published
[quotientIwasawaIntegration](QuotientIwasawaIntegrationProof.md), at
`F.canonicalTopologicalData` and every needed rank. It gives the measure
identity with the actual normalized Haar measures for every compatible
quotient measure. The continuity endpoints are imported from
[IntegrandContinuityProof](IntegrandContinuityProof.md) and
[UnequalRankZeroRowIntegrandContinuityProof](UnequalRankZeroRowIntegrandContinuityProof.md).

## Removing the normalized denominator

`normalizedGenerator_eq_one_of_laurent` uses Laurentness of an entire
value family, not of one integral. Its Laurent span lies in the Laurent span
of `1`, so the normalized-generator equality places the reciprocal of the
polynomial `P` in that span. The published
[normalized reciprocal divisibility theorem](LaurentDivisibilityProof.md),
applied with comparison polynomial `1`, gives `P` dividing `1`. Thus `P`
is a unit and constant; its certified constant coefficient is `1`, giving
`P = 1`.

The ordered assembly handles equal rank with the entire equal-rank value
family. For strict unequal rank it writes the larger rank as
`n + (0 + k + 1)` and uses the entire zero-row block `(0,k)`. A common factor
certificate's existence clause supplies a right-invariance instance and one
compatible quotient measure. Applying the relevant Laurentness theorem at
that measure forces its common polynomial to equal `1`. Substitution into
the original certificate preserves compatible-measure existence, all
compatible measures and every block, without separately reconstructing their
generators.

## Whittaker type, rank orders and factor existence

`TopologicalData.isOpen_principalUnits` proves openness of the actual
principal-unit subgroups from the valuation's open unit sphere and the open
integer ring under `u -> (u-1)/uniformizer^n`, including level zero. The
conductor existence theorem supplies a principal-unit subgroup in the kernel
of every continuous quasicharacter. Monotonicity of subgroup openness then
gives `TopologicalData.quasicharacter_isOpen_ker`. These are consequences of
the existing valuation topology, without an extra nonarchimedean-group
hypothesis.

The published `isOfWhittakerType_quasicharacter_twist_iff` is reused from
[`RankOneTestReduction`](RankOneTestReduction.md). It combines open-kernel
smoothness, the Whittaker-type twist equivalence, and triviality of determinants
on upper-unipotent matrices to preserve full Whittaker type under every
continuous determinant twist. The identical helper statement is retained
under its existing Library name.

The final theorem supplies
[symmetricLPolynomialExists](SymmetricLPolynomialExistenceProof.md), the
published closed symmetric existence theorem, in the original independent
universe order `.{uF,uV,uW}`. The ordered helper obtains the required common
polynomial for each twisted pair from that theorem and twist preservation.
No factor-existence premise remains in the final theorem.

When the original first member has smaller rank, the symmetric assembly
applies this same existence theorem to the twisted original first member
and the original second member, reads its larger-first certificate, and
moves the twist to the larger representation. The ordered analytic argument
then applies with its representation universes reversed. The twist-moving
lemma is derived from simultaneous opposite-twist invariance and inverse-twist
cancellation. Its p-adic lift preserves the existence clause and universal
measure quantifier. Moving the polynomial-one certificate back gives exactly
the original symmetric conclusion. This needs no second existence premise
with swapped universes.

The reusable theorem
`whittakerTypeHighlyRamifiedLVanishing_of_analytic_inputs` retains symmetric
existence as an explicit input while supplying the actual full-torus and
Iwasawa proofs. The final `whittakerTypeHighlyRamifiedLVanishing` supplies
`symmetricLPolynomialExists` to that helper. All analytic, asymptotic, measure
and factor-existence inputs are thereby discharged.

## Original source, provenance and authorship

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 394 read printed pages 385, 390-392, 394 and 403-404. Section 2.1
specifies full Whittaker type; Theorem 2.7 gives the integral and normalized
generator framework; Section 2.12 supplies the opposite-rank convention;
Proposition 2.13 on printed page 404 (PDF page 39, counting the cover as
page 1) uses a fixed finite set of finite functions and ramified scalar
integrals to remove denominators. No source-specific erratum was found in
the available literature checks recorded during development.

This proof implements that finite-function analytic route through the
published asymptotic, tensor, scalar Mellin, conductor, root-coordinate,
compact-integration, quotient-measure and Laurent-divisibility results. The
new integration, twist, conductor-bound and rank adapters are derived
consequences of those interfaces and Mathlib's integral algebra. They are
explained above as implemented; the source need not use this exact
formal decomposition. Only same-representation character transport is used
from `WhittakerGammaAdapters`. No epsilon equation, factor functional-equation
existence, full or two-block L multiplicativity, or Section 9.3 tail
divisibility is used. The target and its imported statement pairs, including
the narrower `HighlyRamifiedStatement`, are unchanged.

Worker 331 authorized reuse of his revision-2 zero-row analytic draft during
development. Its private continuity helpers were subsequently replaced by
the independently published continuity theorem; his contribution to this
assembly remains credited.
