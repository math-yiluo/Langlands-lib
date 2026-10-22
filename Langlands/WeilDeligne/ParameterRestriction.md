# Restriction with the explicit inertia condition

Worker 17 authored this construction module. It imports
`Langlands.WeilDeligne.Parameters` and `Langlands.WeilDeligne.Restriction`.
Let `phi : H → G` be a continuous group homomorphism between groups
with specified topologies, and let `J ≤ H`, `I ≤ G` satisfy
`phi(J) ⊆ I`. The proof constructs the actual continuous map `J → I`
by restriction to the subgroup topologies. The kernel on `J` of the
restricted representation is the inverse image of the original inertia
kernel on `I`, so it is open. This argument needs no continuity of
the group operations, no compactness, and no equality of the two
inertia groups.

`FiniteRepresentation.openInertiaRestrict` and
`WeilDeligneRepresentation.parameterRestrict` retain the already
implemented representation/pair restriction and attach the proved
open-inertia certificate. The pair keeps the original monodromy and
uses the pulled-back norm character `nu.comp phi`. The two class
operations descend through the existing genuine equivalence relation,
using the actual restriction of equivalences.

This is a generic construction along supplied compatible data. An
actual extension of local fields must still supply its continuous
Weil homomorphism, inertia compatibility, and agreement of the
pulled-back norm with the actual local norm. None of those arithmetic
facts is included as a hidden structure field or asserted here.

Source correspondence: Tate, *Number theoretic background*, Corvallis
Part II, §2 and §4.1.2, especially the open-inertia convention on
printed page 20. The present subtype and quotient constructions are
derived directly from restriction of representations and the
topological inverse-image property. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
