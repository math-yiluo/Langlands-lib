# Paired complementary-block transfer: proof

`Langlands.RankinSelberg.unequalRankComplementaryTransfer` proves exactly
[`UnequalRankComplementaryTransferStatement`](UnequalRankComplementaryTransferStatement.md)
for every prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData` and natural numbers `n,r`. The field universe `uF`
and representation universes `uV,uW` are independent. The statement and
its imported modules are unchanged.

For each adjacent pair `(j+1,k)` and `(j,k+1)`, the proof constructs one
`f₀ : (coefficientModel π ℓ).toSubmodule`. That same coefficient satisfies
both literal actual-integral equalities, with the supplied character,
normalized absolute value, compatible quotient measure `μ` and scalar Haar
measure `ν`. The construction uses Whittaker type as stated, including its
smoothness and the given nonzero functional; it adds no irreducibility,
functional equation, continuation, cutoff or interchange hypothesis.

The inner rectangular identities hold at every smaller-group matrix.
Consequently the defined iterated integrals are equal for every complex
parameter. The target asks only for right half-planes, so the proof chooses
both real bounds as zero after choosing `f₀`. This argument makes no
absolute-convergence claim about the outer quotient integral.

## Published inputs and normalization

The proof imports the existing support, integration, smearing, conjugation
and cutoff results by their Lean names:

- [`UnequalRankCompactSupportProof`](UnequalRankCompactSupportProof.md)
  supplies one compact rectangular support, uniform in the smaller-group
  argument.
- [`UnequalRankBlockIntegrationProof`](UnequalRankBlockIntegrationProof.md)
  supplies genuine coefficient integrability from that support, finite
  Schwartz expansion, rectangular last-row Fubini and the actual snoc
  matrix identities.
- [`UnequalRankFourierSmearingProof`](UnequalRankFourierSmearingProof.md)
  supplies one coefficient with both a globally integrable upper-column
  average and its pointwise lower-row Fourier cutoff.
- [`UnequalRankComplementaryConjugationProof`](UnequalRankComplementaryConjugationProof.md)
  identifies the conjugated upper-column translation with the negative
  lower-row translation for the literal unsigned block-Weyl representative.
- [`PadicRowFourierCutoffProof`](../../HarmonicAnalysis/PadicRowFourierCutoffProof.md)
  supplies an even Fourier pair `(Φ,κ)` for the supplied self-dual `ν`:
  `Φ` is one on a prescribed compact set, `κ` is supported in a prescribed
  open neighborhood of zero, and its integral for `rowMeasure ν (n+1)` is
  exactly one.

All rectangular and row measures are products of this same `ν`. In
particular, the last cutoff input already includes its volume factor.
The proof neither changes the Haar measure nor rescales the witness later.
`fourierPair_inverse_of_even` applies the published reflection formula:
the transform with `ψ.scale (-1)` is the transform with `ψ` evaluated at
the negative row. Evenness of `κ` therefore makes the same `(Φ,κ)` a
Fourier pair for the inverse character. This step needs no separate
self-duality hypothesis for that character.

## Choosing the pair and the single witness

`exists_uniform_support_integrable` combines the published uniform support
and coefficient integration theorems at an arbitrary equal large rank.
The supplied p-adic topology gives sigma-compactness and second
countability, providing sigma-finiteness of the scalar Haar and the Borel
instances for finite rectangular products. Thus full rectangular
integrability is established for the actual supplied measure.

Apply this result to `f` at block `(j+1,k)`, and let `C` be the image of
the resulting compact support under last-row evaluation. It is compact.
Put `a = blockWeylAt n r hnr` and let
`D = translatedFirstDualModelEquiv ψ π ℓ a`, the actual first-dual map
followed by the prescribed right translation.

The coefficient `D f` lies in the image model of the inverse-transpose
representation, which is smooth by the published pullback result.
`exists_open_coefficient_invariance` pulls an open subgroup fixing this
coefficient back along the continuous complementary last-row unipotent
map. It gives an open neighborhood `O` of zero on which that right
translation fixes `D f` at every group argument. No topology on the
representation carrier is used. The published normalized cutoff theorem
now supplies the single pair `(Φ,κ)` adapted to `C` and `O`.

Apply the published smearing theorem to `D f` in the inverse-transpose
representation, with the inverse character and this same pair. It gives
one dual-model coefficient `g` with a global upper-column average and
the complementary pointwise cutoff. Define `f₀ = D.symm g`.
`exists_original_of_dual_average` and `dual_average_pullback` use
involutivity and multiplicativity of inverse transpose to give, for every
large-group argument `h`,

```text
f₀(h) = ∫ x, Φ(x) · f(h · L(-x)) ∂rowMeasure ν (n+1),
```

where `L(-x)` is the actual original last-row lower unipotent, reindexed
to rank `r+1`. This integral is genuinely integrable by the global smearing
formula and equality of its integrand with the pulled-back one.
The published complementary conjugation theorem supplies precisely this
negative row. At the same time, `D f₀ = g` retains the complementary
pointwise identity

```text
(D f₀)(B(g',X)) = κ(lastRow X) · (D f)(B(g',X)).
```

Here `B` is the actual complementary block `(k+1,j)`. Thus both formulas
belong to the same `f₀` in the original image model.

## Rectangular integration and actual quotient integrals

`original_rectangular_transfer` applies the published last-row Fubini
theorem to the full rectangular integrand of `f`, whose genuine
integrability was proved above. The published snoc identity splits its
last row as right translation of the zero-last-row matrix; that base
matrix equals the adjacent block `(j,k+1)`. On every nonzero last-row
fiber the row belongs to `C`, so `Φ` is one there.
`reflected_plateau_integral` removes the weight, using evenness of `Φ`
and negation invariance of `rowMeasure ν (n+1)` to handle the negative
row in the average. This proves equality of the original rectangular
integrals at every smaller-group argument.

For the complementary calculation, apply the support/integrability
wrapper to `D f₀` in the inverse-transpose representation. Its Whittaker
type and its nonzero first-dual functional follow from the published
dual-model results. Hence its full rectangular integrand is genuinely
integrable before Fubini is applied. `cutoff_rectangular_transfer`
uses the pointwise cutoff formula, the same snoc splitting, and the
invariance of `D f` wherever `κ` is nonzero. The inner integrand becomes
`κ(x)` times the value at the neighboring complementary block.
`normalized_cutoff_integral` uses the genuine integrability of `κ` and
its mass one to remove that row. This proves the complementary inner
identity in the reverse orientation required for the target.

The `At` versions of the rectangle and witness lemmas retain a fixed
arbitrary large group, substituting equal natural-number ranks and
simplifying the published `finCongr` reindexing. They do not change the
coefficient model.

Finally `unequalRankIntegralAt_congr_inner` applies the published formula
`unequalRankIntegralAt_eq_outer` to both rank wrappers. The fixed test
coefficient and determinant weight are outside the rectangular integral
in that formula. The rank equalities identify the determinant exponents;
the pointwise inner identities then give equal outer integrands.
No interchange with the quotient variable is performed. For the dual
clause this uses exactly the inverse character, `D f` and `D f₀`, and
the unchanged `secondDualFunction ψ n f'.val` specified by
`dualUnequalRankModelIntegralAt`.

The endpoint cases `j=0` and `k=0` use the same snoc and finite-product
formulas. Their zero-row rectangular measure is the published unit point
mass; no additional normalization is introduced.

## Source correspondence and credits

This is an internal proof of the published derived interface. Its
construction follows the lower-row average and complementary Fourier
cutoff in Jacquet–Piatetski-Shapiro–Shalika, *Automorphic Forms on GL(3) I*
(1979), proof of Theorem 4.5, printed pp.197–198, and *Rankin–Selberg
Convolutions* (1983), the Fourier lemma on pp.394–395 and §2.8 on p.395.
The source ranks correspond to Lean ranks `r+1,n+1`. The negative row
and even cutoff account for the project's unsigned Weyl convention.
The all-parameter equality of the defined iterated integrals is an
internal route to the required half-plane equalities, without claiming
outer absolute convergence or attributing that stronger formulation
verbatim to either source.

The registered originals are `jps-1979-gl3-i` and
`jpss-1983-rankin-selberg`, with retained files, fingerprints and source
scope recorded in the statement Markdown. The relevant original formulas
were read visually during development; no source-specific erratum was
found in the available project and Library errata notes.

Worker 623 implemented this assembly from published declarations.
Worker 180 discussed the pointwise inner-integral route and supplied the
independently published block integration helpers. Worker 110 proposed
the normalized even-pair design and supplied the published row Fourier
compatibility result. The proof also reuses the independently published
support, finite-expansion, smearing, dual-model, conjugation and cutoff
results; it imports no unreviewed proof module.
