# Rational representation with presented strict affinoid tests: proof

Author: Worker 247.

The theorem `Langlands.Analytic.StrictTestDomain.rationalRepresentation`
proves `RationalRepresentationStatement`, the target stated and explained in
`RationalRepresentationStatement.md`. Given a complete ultrametric normed
field `K`, a presented strict affinoid algebra `P` and `d : RationalData K P`,
it shows `Represents K d.baseMap d.locus`. The data supply only the
denominator, the finite numerator tuple and their absence of common zeros on
the bounded multiplicative seminorm spectrum of `P`. The representing algebra
`d.algebra` and the map `d.baseMap` are the existing constructed rational
quotient of an enlarged finite Tate algebra and its bounded structural map.

## Proof

The proof is a short assembly of published results. No additional hypothesis
enters it.

1. **Unit ideal.** `RationalFactorization.generatesUnitIdeal_iff_no_common_zero`
   is applied in its reverse direction to the field `d.no_common_zero`. This
   shows that the denominator and numerators generate the unit ideal of `P`.
   That direction realizes a hypothetical proper generated ideal inside the
   kernel of a spectrum point, contradicting the absence of common zeros. The
   unit-ideal equation is therefore derived, not supplied.
2. **Image.** With this equation,
   `RationalLocalization.range_comap_baseMap` states that the range of
   seminorm pullback along the structural map equals the rational locus
   `{x | x(f_j) ≤ x(g) for all j}`. This is the second clause.
3. **Closedness.** The first clause rewrites the locus as this range.
   `RationalLocalization.comap_baseMap_closedEmbedding` says that the pullback
   map is a closed embedding, and the range of a closed embedding is closed
   (`Topology.IsClosedEmbedding.isClosed_range`).
4. **Factorization.** For every presented strict affinoid test algebra `R`,
   take a bounded map `φ : P → R` whose spectrum image lies in the locus. The
   forward direction of `RationalFactorization.factorization_of_no_common_zero`
   then gives exactly one bounded map `ψ : d.algebra → R` with
   `ψ.comp d.baseMap = φ`. That published theorem derives the target
   denominator unit, the fraction tuple and its monomial bounds from the image
   condition. None of these is an input here.

The image condition `HasImageIn` and the representing algebra and map of
`RationalData` agree by definition with the corresponding
`RationalLocalization` expressions. The published theorems therefore apply
without conversion lemmas.

The proof adds no unit-ideal certificate, inverse denominator, bounded
solution tuple or assumed representation. It keeps zero and nonreduced
quotients, empty numerator tuples and trivial scalar valuations, because the
imported results carry no reducedness, nonzero-algebra, positive-arity or
nontrivial-valuation hypothesis. The development check reports only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope relative to the source

The target is a derived specialization of Berkovich, *Non-archimedean
analytic spaces*, Trieste lectures (2009), Definition 2.2.1 and Exercise
2.2.2(ii) on printed/PDF page 9. Definition 2.1.11 on page 8 identifies
morphisms of affinoid spaces with reversed bounded algebra maps. Registered
original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

This result is weaker than the source's affinoid-domain property in two
respects.

- **Strict tests only.** Unique factorization is proved only for test
  algebras that are presented strict affinoids. Berkovich's Definition 2.2.1
  requires it for every morphism from an arbitrary k-affinoid space,
  including non-strict ones. The definition applies the same requirement to
  strictly affinoid domains. That all-affinoid domain property is not
  claimed.
- **Unit radii only.** The locus uses the inequalities `|f_j(x)| ≤ |g(x)|`.
  The source's rational domains allow arbitrary positive radii `p_i`.

The proof also does not identify the enlarged Tate quotient with the source's
relative power-series presentation `A{p⁻¹T}/(gT_i − f_i)`. General affinoid
tests, arbitrary positive radii, structure sheaves, analytic atlases and sites
remain separate work.

`RationalData.generatesUnitIdeal` packages the same no-common-zero implication
for supplied rational data. It is shared by
[`RationalPullbackProof`](RationalPullbackProof.md) and
[`RationalLimits`](RationalLimits.md).
