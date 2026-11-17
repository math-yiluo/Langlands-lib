# Normalizer orbit maps from quotients of closed-embedding schemes

This internal construction takes a full closed-embedding scheme `M` for a
commutative source `A` in `G`, a group `K` of indexed source isomorphisms `α`,
the identity and reversed-composition laws, and faithfulness on every nonempty
relative test scheme. These data define the published free precomposition
action. A supplied `EffectiveQuotient` of that action gives the actual
`normalizerOrbitTarget`, its projection from `M`, and the conjugation map
`normalizerOrbitMap` for any fixed closed embedding.

`LocallyExhaustSourceIsomorphisms A.toGrp α` states the additional input needed
for the exact fiber theorem: every actual source automorphism after arbitrary
base change agrees, near each test-scheme point, with one of the indexed
constant source isomorphisms. The neighborhood is an open immersion containing
that point, and its equality uses actual `HomScheme.evaluate`.

Under that explicit locality input, `normalizerOrbitMap_fibers` proves for
every relative test `T` and points `g,h` that their orbit-map images agree
exactly when `g⁻¹ * h` belongs to the full normalizer subgroup functor.
It does not impose finite generation or multiplicative type on the source;
these are used in the later application to verify the locality input.

For the forward implication, quotient equality gives an open cover with
indexed precomposition relations, by the effective action quotient's local
fiber criterion. Evaluation of the universal closed embedding turns each
relation into equality of conjugation families up to a source isomorphism.
The pairwise criterion from `NormalizerConjugationFibers` gives local
normalizer membership, which glues by the published source-local normalizer
membership theorem.

Conversely, full normalizer-coset membership supplies an actual source
automorphism identifying the conjugation families. The locality input
identifies it near each point with an indexed automorphism. The universal
property of `M` gives the corresponding parameter equality; invariance of
the quotient projection then gives equality of the orbit maps on those
neighborhoods and hence globally.

If `K` is finite and `M.scheme.left` is quasi-affine, the supplied effective
quotient target is quasi-affine by `normalizerOrbitTarget_isQuasiAffine`.
Quotient existence and the locality premise are separate explicit inputs.
All provenance is derived from the imported closed-embedding, finite-action,
normalizer, and conjugation-family constructions.
