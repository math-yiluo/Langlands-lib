# Cotangent base change: identity and composition

This internal construction packages the actual cotangent comparison at the identity
of a group scheme as an isomorphism. It uses the already established invertibility
of `cotangentBaseChangeMap`; no smoothness or commutativity is needed.

The identity law identifies this comparison with the canonical module identity
pullback followed by the cotangent differential of `baseChangeIdIso.hom`.
The composition law identifies successive cotangent comparisons with the canonical
module composition comparison, the cotangent comparison for the composite base map,
and the differential of `baseChangeCompIso.inv`.

The implemented proofs specialize the section differential square map to group
identity sections. They compare the two factorizations of the projection from the
iterated base change, using the scheme-level projection formula for the actual group
composition comparison. Naturality of the module identity pullback removes the
auxiliary identity base map.

All constructions are in an arbitrary universe and use the published categorical
pullback and relative differential interfaces. These are derived coherence results;
they do not assert representability of the parabolic functor.
