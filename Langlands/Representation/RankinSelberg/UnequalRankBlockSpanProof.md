# Equality of adjacent unequal-rank JPSS Laurent spans

Author: Worker 180.

`Langlands.RankinSelberg.unequalRankAdjacentBlockSpan.{uF,uV,uW}` proves
the published [UnequalRankAdjacentBlockSpanStatement](UnequalRankBlockSpanStatement.md).
Its complete telescope consists of implicit `{p : ℕ}` and `[Fact p.Prime]`,
then explicit `F : PadicField.{uF} p`, `T : F.TopologicalData`, and
`n r : ℕ`. Its result is exactly
`UnequalRankAdjacentBlockSpanStatement.{uF,uV,uW} F T n r`.

For every allowed `j,k` with `r = n + (j+k+2)`, this gives equality of the
Laurent spans of `unequalRankValuesAt (j+1) k` and
`unequalRankValuesAt j (k+1)`. The proof retains every supplied topology,
nontrivial continuous unitary additive character, compatible quotient measure,
and regular scalar additive Haar measure. It covers all representations of
Whittaker type quantified by the target, with independent carrier universes
`uV` and `uW`, and every pair of its nonzero Whittaker functionals. There is
no irreducibility assumption or topology on either representation carrier.
The target's rank inequalities and compatibility hypotheses are retained;
the integral comparison itself needs less.

## Forward transfer by last-row integration

The imported
[UnequalRankBlockIntegrationProof](UnequalRankBlockIntegrationProof.md)
provides the block factorization, finite coefficient integration,
integrability, product-measure splitting, zero-row identity, and outer-integral
formula. Its finite integration theorem uses the published
`Langlands.HarmonicAnalysis.exists_finite_schwartz_expansion` from
`CompactCosetExpansion`: a uniformly locally constant, compactly supported
function into an algebraic function space is a finite sum of scalar Schwartz
functions times sampled values. All samples are chosen before the parameters.

For a fixed first coefficient `f`, the published
[unequalRankCompactSupport](UnequalRankCompactSupportProof.md) supplies one
compact set supporting all rectangular block evaluations, uniformly in the
smaller general-linear element. Projecting that set onto its last row gives
compact support for the family

```text
x ↦ (g,Y ↦ f(B(g,snoc Y x))).
```

The block factorization writes these evaluations as right translates by a
continuous last-row unipotent map. Smoothness gives uniform local constancy
of the orbit map of a preimage of `f` in the original representation.
The finite expansion and its scalar integrals therefore give an actual
finite linear combination of vectors in that same algebraic carrier.
Its coefficient `f₀` satisfies, for every `g,Y`,

```text
f₀(B(g,snoc Y 0)) = ∫ x, f(B(g,snoc Y x)) ∂rowMeasure ν (n+1).
```

The full rectangular coefficient is integrable by the imported compact-support
integration theorem. The finite-coordinate measurable equivalence separates
the final row from all earlier rows and carries the actual rectangular product
measure to the corresponding product measures. Fubini and the zero-last-row
matrix identity then give the neighboring rectangular integral of `f₀`.
`exists_adjacent_block_integral_coefficient` implements this step, including
`j = 0`, when there are no earlier rows.

The `blockMatrixAt` wrapper is imported from
[UnequalRankBlockMatrix](UnequalRankBlockMatrix.md). Its natural-number
equalities transport only the large-rank types. The zero-row comparison is
the separate proved matrix identity, rather than a consequence of arithmetic
transport alone.

## Reverse transfer by a small cutoff and Fourier smearing

The companion [UnequalRankSmearingProof](UnequalRankSmearingProof.md)
constructs a Schwartz cutoff `Φ` of integral one for the supplied row
measure, supported on parameters whose right unipotent translations fix
the original coefficient at every group element. Consequently

```text
Φ(x) f(B(g,snoc Y x)) = Φ(x) f(B(g,snoc Y 0))
```

for every `x`, including points where `Φ(x) = 0`.

The published
[padicRowFourierSurjectivity](../../HarmonicAnalysis/PadicRowFourierSurjectivityProof.md)
supplies an actual Schwartz kernel `κ` for this `Φ`, the actual character,
and the supplied scalar Haar `ν` in dimension `n+1`. Its conclusion uses the
plus-sign pairing and exactly `rowMeasure ν (n+1)`.
The published
[unequalRankFourierSmearingStatement](UnequalRankFourierSmearingProof.md)
then constructs a coefficient `f₁` in the original model with pointwise value

```text
f₁(B(g,X)) = Φ(X(last j)) f(B(g,X)).
```

That theorem also retains the global scalar averaging formula for the same
coefficient. Its finite averaging constructs an algebraic vector; no vector
valued Bochner integral is used.

The compact-support theorem applies again to this constructed `f₁`.
Fubini is therefore justified for its full rectangular integral.
The displayed fixing identity and `∫ Φ = 1` remove the last row.
The same zero-row matrix identity identifies the result with the neighboring
rectangular integral of the original `f`.
`exists_reverse_adjacent_block_integral_coefficient` implements this reverse
transfer.

## Quotient integrals, continuations, and final assembly

The imported `unequalRankIntegralAt_eq_outer` writes each existing integral
using a representative of every quotient point. Its second coefficient and
determinant weight are constant in the rectangular variable. The two
determinant shifts are equal. Both constructed coefficients therefore
preserve the scalar iterated integral for every second Whittaker function
and every complex parameter at once.

This comparison uses the existing totalized scalar integrals and assumes
neither quotient convergence nor existence of rational continuations.
When a rational continuation already witnesses membership in one value set,
the equality transfers that same rational function, denominator condition,
and right half-plane to the other value set.
`adjacent_values_eq_of_support_cutoff` thus proves equality of the actual
rational-value sets under its displayed support and cutoff premises.
Applying `zetaSpan` gives the required Laurent-span equality.

`adjacentBlockSpan_of_support_fourier` specializes this generic reduction
to the supplied p-adic data. It installs exactly `T.topology`,
`T.valuativeRel`, `T.localField`, `T.fieldT2`,
`T.sigmaCompactSpace`, and `T.secondCountableTopology`, together with the
target's Borel measurable structures. Finite-product Borel and measure
instances come from these certificates. Total disconnectedness follows
from `ValuativeRel.nonarchimedeanRing`, using the equality of its valuation
topology with the supplied topology.

`adjacentBlockSpan_of_fourier` discharges uniform support using
`unequalRankCompactSupport.{uF,uV}` at every `n,j+1,k`.
Finally, `unequalRankAdjacentBlockSpan` applies this reduction to
`padicRowFourierSurjectivity F T (n+1)`. Both intermediate premises are
proved by the imported public theorems, so the final theorem has no support,
cutoff, Fourier-existence, or self-duality hypothesis.

## Supplied measures and normalization

Both block measures are products of the same supplied scalar Haar `ν`.
Every row integration and finite average uses those actual measures.
The product splitting introduces no scalar factor, including the
zero-row case with unit point mass. The normalized small cutoff divides
by the positive finite mass of its compact open support for this measure.
The quotient measure remains the supplied `μ` throughout.

The Fourier-surjectivity dependency handles the difference from the source's
self-invariant Haar convention. It first chooses a self-dual reference scalar
Haar, proves row closure and inversion for that reference, and uses the
positive finite ratio between the supplied Haar and the reference.
In dimension `d` its kernel is rescaled by the inverse `d`th power of that
ratio. Its conclusion is the actual Fourier equality for the supplied
measure, which is exactly what the smearing proof consumes.
No self-duality condition is imposed on `ν`, and the adjacent-span proof
does not substitute a normalized measure for either block measure.

## Original sources and internal provenance

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`.
Theorem 2.7(i)–(ii), printed pp.390–391, asserts block-independent generators
for representations of Whittaker type. Lemma 2.6, pp.389–390, supplies the
uniform rectangular support used in the unequal-rank argument beginning
on p.393. The Fourier-smearing lemma is on pp.394–395. The final comparison
on p.395 proceeds through auxiliary Schwartz-cutoff ideals.
Our adjacent indices `j+1` and `j` are its `a` and `a-1`.

The referred source, *Automorphic Forms on GL(3) I* (1979), registered as
`jps-1979-gl3-i`, gives Proposition 4.1.4 and Lemma 4.1.5 on pp.188–190.
Its four inclusions use compact support, smoothness, compact-open averaging
divided by volume, and Fourier smearing. These original pages and formula
images were read for this work. Their retained files and hashes are recorded
in the unchanged target's Markdown.

The implementation combines the same operations into direct transfers of
coefficients and equalities of integrals, without introducing the auxiliary
ideals. Its stronger intermediate value-set equality follows from these
explicit transfers, rather than being attributed as a separate assertion
of the originals. Finite scalar integration, product-measure equivalences,
and the p-adic assembly are internal implementation steps.
The shared block-integration source proofs were authored by Worker 180
and extracted into the public package by Worker 52. The finite-expansion
dependency was coauthored by Worker 180 and Worker 451. Their published
theorems are imported by name without copied declarations.

The proof assumes no analytic-existence theorem, common normalized generator,
or functional equation. The target pair and its import closure are unchanged.
