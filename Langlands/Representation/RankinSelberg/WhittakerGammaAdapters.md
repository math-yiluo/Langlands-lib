# Proof of the Whittaker character and fixed-monomial epsilon adapters

The theorem `Langlands.RankinSelberg.whittakerGammaAdapters` has exactly the
published proposition
`Langlands.RankinSelberg.WhittakerGammaAdaptersStatement.{uF,uV,uW}` as its type.
That proposition is the statement pair
`Langlands.Representation.RankinSelberg.WhittakerGammaAdaptersStatement`, which this
module imports unchanged. The field universe `uF` and the carrier universes `uV`
and `uW` stay independent. The final proof splits the conjunction into its three
closed components. For each component it introduces all the quantified data and
instances exactly as the statement orders them, then applies one of the helper
theorems below. The proof uses no further hypotheses and no new epsilon relation.

## Same-representation character transport

`isOfWhittakerType_standard_iff_inverse ψ π` proves
`IsOfWhittakerType n (standardCharacter ψ n) π ↔
IsOfWhittakerType n (inverseStandardCharacter ψ n) π`. Its hypotheses are those of
`WhittakerTypeCharacterTransportStatement`: a field with a topology and
`IsTopologicalRing`, a unitary additive character, any `n`, and an actual
representation of `GL_(n+1)(F)` on a complex vector space.

The proof first builds a linear equivalence
`glFunctionals ψ n π ≃ₗ[ℂ] glInverseFunctionals ψ n π`. It starts from the
published `characterChangeFunctionalEquiv ψ π (-1)`, which is translation by
`π(d_{-1})` from the standard functionals for `ψ` to those for `ψ.scale (-1)`.
The codomain is unfolded to the functionals for
`standardCharacter (ψ.scale (-1)) n`. Then the published
`standardCharacter_scale_neg_one` rewrites that character to
`inverseStandardCharacter ψ n`. `IsOfWhittakerType` is the conjunction of
admissibility, finite generation of `π.asModule`, and a linear equivalence of the
functional space with `ℂ`. Both directions keep the first two conjuncts verbatim,
because they concern the same `π`. For the third conjunct, the forward direction
composes the inverse of this equivalence with the given equivalence to `ℂ`. The
reverse direction composes the equivalence itself with the given one.

## Equality of coefficient models

`coefficientModel_eq_of_whittakerType` assumes `IsOfWhittakerType n θ π` for an
arbitrary character `θ` of the upper unipotent subgroup. It shows that any two
functionals `ℓ` and `ℓ'` with nonzero underlying linear maps have equal coefficient
models, `coefficientModel π ℓ = coefficientModel π ℓ'`. The proof compares the
underlying submodules by antisymmetry. The published `IsOfWhittakerType.eq_smul`
writes `ℓ = c • ℓ'` for some `c : ℂ`. Then the published
`coefficientModel_smul_le ℓ' c` gives one inclusion. The other inclusion follows
symmetrically from `ℓ' = c • ℓ`. Injectivity of
`Subrepresentation.toSubmodule` turns the submodule equality into equality of the
subrepresentations.

## Fixed-monomial epsilon adapters

`equalRankEpsilonFactor_of_equation` has the hypotheses of
`EqualRankEpsilonUniformityStatement`: full standard Whittaker type of `π`, full
inverse-standard Whittaker type of `σ`, and nonzero functionals `ℓ` and `ℓ'`. It
also assumes
`EqualRankEpsilonEquation q ψ abv (unipotentQuotientHaar F n) ν π σ ℓ ℓ' c m`.
It proves `IsEqualRankEpsilonFactor q ψ abv ν π σ (c, m)` by supplying its four
conjuncts.

1. The measure conjunct is
   `⟨unipotentHaar_isMulRightInvariant F n, unipotent_compatibleMeasureExists F n⟩`.
   These are the published right invariance of the unipotent Haar measure and the
   compatibility of the constructed quotient measure.
2. The functional-existence conjuncts are witnessed by the supplied `ℓ` and `ℓ'`.
3. For the uniform conjunct, take any right-invariance instance, any compatible
   quotient measure `μ`, and any nonzero functionals `ℓ₂` and `ℓ₂'`. The
   published `unipotentQuotientHaar_unique F n μ hμ` rewrites `μ` to
   `unipotentQuotientHaar F n`. By the coefficient-model lemma, the model of `ℓ`
   equals that of `ℓ₂` and the model of `ℓ'` equals that of `ℓ₂'`. The published
   `EqualRankEpsilonEquation.congr_model` then transports the supplied equation
   from `(ℓ, ℓ')` to `(ℓ₂, ℓ₂')`, with the same `c` and `m`.

`unequalRankEpsilonFactor_of_equation` is the same argument for ranks
`r + 1 > n + 1`, with `hnr : n < r`. Here `π` has standard Whittaker type of rank
`r + 1`, and the hypothesis is `UnequalRankEpsilonEquation hnr` at
`unipotentQuotientHaar F n`. It proves
`IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ (c, m)` and uses
`UnequalRankEpsilonEquation.congr_model` in the last step. That lemma transports
the whole equation as one proposition. It therefore keeps the equation's
quantification over every `j k`, every `r = n + (j + k + 1)`, the rectangular
product measures, the complementary dual block, and the common polynomials and
central sign. Only the smaller group's quotient measure occurs, and it is again
identified with `unipotentQuotientHaar F n`.

Neither adapter changes `q`, `abv`, `ν`, `c` or `m`. Neither proves that an epsilon
equation exists: the equation for the specified pair at the constructed measure
remains a premise. `[BorelSpace F]` is introduced by the final proof but not used.

## Provenance and credit

The character-transport argument follows H. Jacquet, I. I. Piatetski-Shapiro and
J. A. Shalika, *Rankin-Selberg Convolutions*, Amer. J. Math. 105 (1983), §2.1,
printed pp. 385–386. The source is registered as `jpss-1983-rankin-selberg`. The
existing functional equations have their provenance in Theorem 2.7 (printed
pp. 390–391). The two uniformity adapters are internal packaging of published
Library relations, not separately quoted theorems of that paper.

This module ports Worker 471's unreviewed parent-task draft
(`ce47e251-5d9a-4cb5-b94c-b3884bcc42b0`, draft revision 3). The port renames the
namespace and drops an unused import. Worker 640 designed the published interface.
Workers 31, 43, 103 and 216 supplied the reused navigation and assembly route.
