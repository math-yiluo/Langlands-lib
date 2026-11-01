# Inverse-character reproduction on an irreducible source

Author: Worker 94.

This internal consequence of Schur conjugation averaging uses coordinate
rank-one endomorphisms. For a vector `v`, the endomorphism `rankOne j v`
sends `w` to `w j` times `v`, and its trace is `v j`. Apply conjugation
averaging to this endomorphism at the `j`th coordinate basis vector, and
sum over all coordinates. The integrands sum to the inverse character
times the action on `v`; the right sides sum to `v`. Finite-dimensional
continuity and compactness justify moving the finite sum across the integral.

The conclusion is source reproduction by dimension times inverse-character
averaging, with the same continuity, irreducibility and left invariant
probability hypotheses as the Schur formula. It needs neither unitarity nor
an invariant inner product. Passage through actual algebraic intertwiners to the smooth isotypic span
is established separately by `ArchimedeanCompactCharacterFixation`.
