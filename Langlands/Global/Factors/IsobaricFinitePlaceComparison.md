# Finite-place comparison for isobaric automorphic subquotients

## Embedded local types

`OperatorSubquotient.isFinitePlaceIsotypic_of_injective` proves that if an
irreducible representation embeds into the restriction of an irreducible
operator subquotient to a finite place, the images of the intertwiners from
that representation span the entire restriction. The given embedding makes
their sum nonzero. Local translations preserve the sum, and postcomposition
by operators in the local centralizer also preserves it. These two actions
are jointly irreducible by `isJointlyIrreducible_localCentralizerOperators`.
This is the isotypic restriction used in Flath (1979), end of the proof of
Theorem 1, p. 180 (one-based PDF p. 176), in the case where an irreducible
local embedding is supplied.

`OperatorSubquotient.nonempty_local_equiv_of_injective` pulls the isotypic
sum back along a second embedding. Its irreducible source is entirely of
the first type and hence is equivalent to the first source.

## Equivalent cuspidal realizations

`CuspidalSpectralPresentation.nonempty_localComponent_equiv_of_equivalence`
restricts a full cuspidal equivalence to the local translations. It
transports one of the presentation embeddings across that equivalence and
uses `OperatorRealization.nonempty_local_equiv_of_injective` to compare the
two embeddings in the resulting common realization. This implements
independence of the finite-place type from the cuspidal realization and
its presentation, using the same isotypic restriction argument.

## Comparison of isobaric sums

`nonempty_finitePlace_isobaricSum_iso` takes a bijection between the two
cuspidal families with equality of the corresponding positive-rank cuspidal
classes. Within each matched pair, the class equality first identifies the
rank indices. At that common rank it gives an equivalence of the full
operator realizations. The presentation comparison then gives an isomorphism
of their finite-place components.

The supplied `IsIsobaricSum` witnesses give an inducing multisegment for
each component. Rodier's classification identifies the multisegments of
the isomorphic components through `multisegmentHeadClassification`. The
bijection reindexes the sum of multisegments, so a second application of
the classification gives an isomorphism of the supplied isobaric sums.
The union of the component data is the local isobaric construction in
Getz–Hahn (2024), §10.6, (10.33), p. 284 (one-based PDF p. 296). The
multisegment classification is Rodier (1982), §4.3, Theorem 3(b),
pp. 211–212 (one-based PDF pp. 12–13).

`IrreducibleOperatorSubquotient.exists_common_finitePlace_isotypic_of_isobaricSum`
uses the finite-place embeddings supplied by the two `IsCuspidalIsobaricSum`
witnesses. It composes the second embedding with the isomorphism of the
sums and applies isotypy from injectivity to both embeddings. The resulting
common irreducible admissible object supplies the finite-place type used
in the local determination argument. The two spectral presentation
universes remain independent.
