# Canonical symmetric gamma construction inputs from Whittaker type

Author: Worker 471.

`Langlands.RankinSelberg.whittakerTypeGammaConstructionInput` proves exactly
`Langlands.RankinSelberg.WhittakerTypeGammaConstructionInputStatement.{uF,uV,uW}`.
It covers every prime, canonical p-adic field, nontrivial unitary additive
character, supplied self-dual scalar Haar measure and pair of positive ranks.
The two actual representation carriers have independent universes. Its only
representation hypotheses are the standard Whittaker types already in the
target. The statement and its imported interfaces are unchanged.

The implementation assembles four published JPSS proof declarations:
`equalRankAnalytic`, `unequalRankAnalytic`, `equalRankFunctionalEquation` and
`unequalRankFunctionalEquation`, from their respective `Proof` modules in
`Langlands.Representation.RankinSelberg`. Character and epsilon uniformity
use the published `WhittakerGammaAdapters` module. The following explains the
assembly rather than reproving those substantive results.

## The ordered construction input

`padicPairGammaConstructionInput_of_whittakerType` handles ranks `r+1 ≥ n+1`,
with standard type for the first representation and inverse-standard type for
the second. It installs the canonical topology, valuation, local-field and
Borel structures used by `PadicPairGammaConstructionInput`, and uses
`unipotentQuotientHaar_isCompatible` for its actual canonical quotient measure.

Its local argument `hA` establishes `PairAnalyticInput` for any character and
pair of representations with those types. For equal ranks it applies
`equalRankAnalytic` to every nonzero functional pair. For unequal ranks it
applies `unequalRankAnalytic` to every permitted rectangular block, using the
block's rank equality. These conclusions retain convergence, rational
continuation, denominators and normalized generators, including all equal-rank
Schwartz–Bruhat tests.

The proof uses `hA` first on the original pair at `ψ` and then on the actual
inverse-transpose pullbacks at `ψ.scale (-1)`. The published
`isOfWhittakerType_firstDual` and `isOfWhittakerType_secondDual` supply the
required dual types. Both analytic applications retain the same canonical
quotient measure and the same supplied scalar Haar measure `ν.val`. The
analytic theorems permit arbitrary scalar Haar measure; this step needs no
self-duality transport to the inverse character.

For epsilon existence, Whittaker type first supplies a nonzero functional on
each representation. The appropriate published functional-equation theorem,
applied to that pair and to the original character, supplies one unit `c` and
one integer `m`. The equivalences
`exists_equalRankEpsilonEquation_iff` and
`exists_unequalRankEpsilonEquation_iff` express its normalized conclusion as
the corresponding fixed-monomial equation. The adapters
`equalRankEpsilonFactor_of_equation` and
`unequalRankEpsilonFactor_of_equation` then give a certificate for those
same constants over every nonzero functional pair and every compatible
quotient measure. The unequal-rank certificate is uniform in the rectangular
block. Thus the existential witnesses precede all those universal choices.
The imported adapters use equality of the actual coefficient models and
uniqueness of the compatible quotient measure; choosing one functional pair
alone would not supply this uniform conclusion.

`isPairEpsilonFactor_self` or `isPairEpsilonFactor_of_lt` converts that
certificate to the existing `PairEpsilonFactorExists`. The normalized
equations retain the central sign, all Fourier tests in equal rank, and the
complementary dual block in unequal rank. The unequal-rank functional-equation
theorem already includes the shared original and dual generators, so this
assembly requires no separate common-generator premise.

Finally, the proof packages the rank inequality, supplied self-duality,
uniform epsilon existence, original types and both analytic inputs into the
existing `PadicPairGammaConstructionInput`. The dual Whittaker types are
derived by the existing construction interface.

## Both original rank orders

The closed theorem splits on `n ≤ r`, exactly as
`PadicSymmetricGammaConstructionInput` does. In the first branch it uses the
ordered theorem on `(π, σ)` at universes `uF,uV,uW`. In the other branch it
uses the same theorem on `(σ, π)` at universes `uF,uW,uV`. This exchanges the
actual representations without identifying their carriers or universes.

In each branch, `isOfWhittakerType_standard_iff_inverse` supplies the required
inverse-standard type for the representation placed second, from its original
standard type. This is full Whittaker-type transport on that same
representation; the adapter uses character change at `-1` and
`standardCharacter_scale_neg_one`, preserving admissibility and finite
generation. Reducing the existing rank-order definition gives the target.
Equal ranks use the first branch.

## Mathematical provenance

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Section 2.1, printed pp.385–386, gives the Whittaker-type and character/dual
conventions; Theorem 2.7, printed pp.390–391, gives the analytic and normalized
functional-equation inputs; Section 2.12, printed p.403, gives the
larger-rank-first convention. Those passages were visually checked in the
retained scan. No separate source erratum note was present in the checked
project and Library locations.

This theorem is an internal consequence of those results in the Library's
canonical p-adic interfaces. The imported analytic proofs are due to Workers
64 and 329, and the functional-equation proofs to Workers 216 and 103.
The published adapter companion records the contributions of Workers 31, 43,
103, 216, 471, 640 and 724. Their paired Markdown explains the substantive
proofs and transport arguments used here. This assembly proves the
construction-input proposition; factor construction and later comparison
identities are separate declarations.
