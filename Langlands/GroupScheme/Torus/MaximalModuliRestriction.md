# Restricting a universal torus family to an open maximal locus

Worker 586.

This internal construction isolates the categorical part of restricting a
universal family of closed relative tori to its maximal locus. The open-locus
hypothesis in `isUniversalMaximal_openFamily` requires that, for every test
scheme and parameter map, the evaluated actual torus is fibrewise maximal
exactly when that map has image in the chosen open subset. Establishing the
existence and openness of such a locus is a separate geometric obligation.

`IsUniversalMaximal` is the all-test-scheme universal property for closed
relative tori which are maximal on every residue fibre. `openModuli` gives
the chosen open subscheme its composite map to the original base;
`openInclusion` is its actual inclusion over that base. `openFamily` is the
original family pulled back along this inclusion with the canonical ambient
pullback comparison. Its source is the actual commutative group-scheme
pullback. The construction preserves the closed relative-torus conditions
and preserves smoothness of the parameter scheme over the base.

For the universal property, classify the given maximal torus using the
original universal family of all tori. Equality of represented subgroups
transports fibrewise maximality to that evaluated family. The open-locus
hypothesis makes the classifying map factor through the open subscheme.
Composition of actual family evaluation proves the required subgroup equality.
Uniqueness follows from the original universal property and the monomorphism
of the open immersion.

The range-invariance lemma constructs the unique isomorphism between closed
representatives of the same subgroup functor. Pulling this isomorphism to each
residue fibre transports maximality there. Thus the argument uses equality
on every test scheme, rather than equality on geometric points. All inputs
are published subgroup representation and evaluation infrastructure; no
additional external mathematical assertion is introduced.
