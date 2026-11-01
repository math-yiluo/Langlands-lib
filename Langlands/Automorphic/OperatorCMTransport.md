# Actual CM images of full automorphic operator realizations

This internal construction restricts the existing CM argument pullback to the
actual function subspaces in `OperatorRealization`. It combines the proved
stable-core and whole-operator covariance in `StableAutomorphicCMTransport`
with the existing `OperatorRealization` and `CuspidalOperatorRealization`
carriers. The invariant-subspace map/comap argument reuses
`Langlands.conjugatedSubrepresentationOrderIso`, extracted unchanged into
`Representation/SubrepresentationConjugation` from the identical helper in
`OperatorDeterminantTwist`. No new
identification with a literature-defined object is claimed.

For an actual CM number field `K : Type uK` and any natural rank `n`,
`OperatorRealization.complexConjOrderIso` maps every actual embedded realization
onto its image under `StableAutomorphicFunctions.complexConj n`. Invariance
follows from the proved whole-algebra covariance and the actual algebra
automorphism `cmOperatorConjugation`; the inverse is the linear preimage.
`S.complexConj` is this image, with its exact mapped submodule displayed by
`complexConj_toSubmodule`. Applying this construction twice gives the original
embedded subspace, proved by composition of submodule images and involutivity
of the actual function pullback.

`S.complexConjEquiv` is the actual continuous complex-linear equivalence from
`S.Space` onto `S.complexConj.Space`. Its underlying forward and inverse maps
both conjugate the argument of the represented function. Topologies are the
existing subspace topologies inherited from compact-open continuous functions;
complex values are unchanged. The form inclusion commutes with the previously
constructed `AutomorphicForms.complexConj`. Forward and inverse evaluation are
both exactly substitution of `CMConjugation.adelicConj K n g` for `g`.

The covariance identities identify the entire operator action and its three
generator families. If `C` is the constructed image equivalence and `c_A` is
`cmOperatorConjugation`, they read

`S.complexConj.representation a (C f) = C (S.representation (c_A a) f)`.

The finite and standard compact parameters transform by the actual
`CMConjugation.finiteConj` and `CMConjugation.compactConj` maps. The differential
parameter transforms by `ArchimedeanLieTransport.envelopingEquiv` for the CM
field involution, with complex coefficients fixed. These formulas concern the
existing genuine differential operators on actual functions.

`complexConjSubrepresentationOrderIso` is the resulting order equivalence on
all invariant subspaces of the restricted representations, again with image
and preimage as inverse maps. Its simple-order criterion preserves and reflects
full-operator irreducibility. The actual embedded central-character condition
is preserved and reflected from `chi` to `chi.complexConj`, where
`chi.complexConj x = chi (ideleClassComplexConj x)`; no inversion or conjugation
of character values occurs.

With compactness of the additive adele quotient explicit,
`complexConj_isCuspidal_iff` preserves and reflects the existing normalized
constant-term vanishing condition. It follows by the actual continuous cusp
covariance and surjectivity of the image equivalence. The constructor
`CuspidalOperatorRealization.complexConj` therefore gives an actual irreducible
cuspidal realization of the same positive rank `r + 1`. Its involution and
central-character reflection are proved. Nonzeroness is inherited from the
existing irreducible cuspidal carrier, without any occurrence assumption.

No equality of the stable core with all forms, arbitrary-class occurrence,
classification, self-duality, spectral existence, tensor presentation, or
isomorphism-class transport is asserted here. The map on embedded subspaces
and its covariance are constructed; descent to full equivalence classes and
further presentation transports are separate constructions.
