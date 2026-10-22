# Epsilon construction from square-integrable classification

This module constructs the nongeneric epsilon pair using the existing
square-integrable classification and exhaustion propositions, together with
explicit block-factor existence. It proves the datum-independence step inside
the construction. It does not prove those classification or existence inputs.

The entry point is
`Langlands.RankinSelberg.langlandsPairEpsilonFactorOfClassification`.
Its output is an actual pair `e : ℂˣ × ℤ` with the existing
`IsLanglandsPairEpsilonFactor` certificate.

## Provenance and imported interfaces

This is derived content. It composes the existing definitions and propositions
in `RankinSelberg/LanglandsFactors`,
`RankinSelberg/PadicPairFactors`, and
`Classification/MultisegmentClassificationStatement`. No new interpretation
of an original-source theorem, analytic assertion, or classification statement
is introduced.

The epsilon relation and product convention come from `LanglandsFactors`.
The product multiplies complex unit coefficients and adds integer exponents,
so that it represents the product of the corresponding epsilon monomials.
The imported `SquareIntegrableLanglandsClassification` proposition says that
isomorphic irreducible quotients have block families matching by a finite
permutation, equal block ranks, and actual isomorphisms after rank transport.
The imported `SquareIntegrableLanglandsExhaustion` proposition supplies a
square-integrable Langlands head for an irreducible representation. Their
original-source provenance remains documented in their existing paired
Markdown; here both propositions are hypotheses.

The helper results below are intrinsic to this construction. They use
`IsPadicSymmetricEpsilonFactor.congr_equiv`,
`IsPadicRankEpsilonFactor.unique`, `SmoothRep.equivOfIso`,
Mathlib's finite-product and finite-sum reindexing lemmas, and the already
published conditional constructor `langlandsPairEpsilonFactor`.

## Scope, topology, and universes

Fix a prime `p`, a finite p-adic field `F : PadicField.{uF} p`, its canonical
topological data, a `UnitaryAdditiveCharacter` `ψ`, and an additive Haar measure
`ν` for the associated Borel structure. The same `F`, `ψ`, and `ν` occur in
every block factor and every comparison. The code adds no self-duality
assumption or proof; the existing epsilon relations and the block-existence
input retain their own conditions.

The representation ranks are `r + 1` and `t + 1`, in either order, and their
carriers have universes `max uF uV` and `max uF uW`. The two carrier parameters
are independent. The imported classification statements quantify over blocks
at these saturated universes too. Consequently, the entry point's block
existence and output certificate instantiate `LanglandsFactors` at universe
arguments `.{uF, max uF uV, max uF uW}`. It makes no claim to obtain the same
classification input for blocks in an arbitrary smaller universe.

The general representation-equivalence lemma permits independent source and
target carrier universes. The block-matching lemma uses two data of the same
carrier universe on each side, as required for their categorical isomorphisms.
Its natural total ranks may include zero; its proof is just a comparison of
already certified finite products.

## Product comparison

`IsPadicRankEpsilonFactor.congr_equiv` extends the existing equivalence
invariance through the natural-rank adapter. It reduces to reflexivity when
either rank is zero, where both relations are false. At two positive ranks it
uses `IsPadicSymmetricEpsilonFactor.congr_equiv`.

The private `rankEpsilonFactor_congr_iso` helper first eliminates the two
equalities of ranks. It then turns the actual smooth-representation
isomorphisms into representation equivalences and applies the preceding lemma.
This accounts explicitly for the dependent transport of a block between equal
general linear ranks.

`epsilonFactorProduct_reindex` proves invariance under bijections of both
finite indexing types. It compares the two coordinates of the output pair
separately: `Fintype.prod_equiv` and `Equiv.prod_comp` reindex the coefficient
product, while `Fintype.sum_equiv` and `Equiv.sum_comp` reindex the exponent
sum. Empty indexing types are covered by these same identities.

`squareIntegrableDataEpsilonFactor_eq_of_matching` takes four data
`d₁, d₂, d₁', d₂'`, a matching of `d₁` with `d₂`, a matching of `d₁'` with
`d₂'`, and two certified products `e₁, e₂`. It extracts each product's entire
family of block factors. At every block pair, rank transport and the two
isomorphisms carry the first epsilon certificate to the matched blocks.
Uniqueness of the block epsilon factor identifies its value with the second
family's value. Function extensionality identifies the first family with the
reindexed second family, and `epsilonFactorProduct_reindex` gives `e₁ = e₂`.
This lemma assumes neither analytic existence nor a classification theorem.

## Independence and construction

`langlandsPairEpsilonDataIndependence_of_classification` takes the published
`SquareIntegrableLanglandsClassification` proposition at each carrier
universe. Given any two presenting data for `π`, it applies classification
to the identity isomorphism of `π` to obtain their block matching. It does
the same for `σ`. The product-comparison lemma then proves exactly
`LanglandsPairEpsilonDataIndependence`. In particular, the proof needs only
the direction of classification from isomorphic quotients to matching blocks.

`langlandsPairEpsilonFactorOfClassification` takes:

1. Irreducibility of the two smooth representations.
2. The existing exhaustion proposition at each of the two carrier universes.
3. The existing classification proposition at each of the two carrier universes.
4. `LanglandsPairEpsilonBlockExistence` for the pair.

Exhaustion produces a datum and head certificate for each representation.
The published `IsLanglandsHead.isLanglandsQuotient` implication gives the
two quotient witnesses required by `langlandsPairEpsilonFactor`.
The constructor supplies these witnesses, the explicit block-existence
hypothesis, and the newly proved datum-independence result to that existing
constructor. The returned coefficient and exponent therefore carry the
existing universal block-product certificate for every presenting datum pair.
Its uniqueness is already provided by `IsLanglandsPairEpsilonFactor.unique`.

No classification, block-factor existence, generic/nongeneric compatibility,
or transformation law is proved by this module. The improvement is the removal
of datum independence as an additional unproved input once the published
classification propositions are supplied.
