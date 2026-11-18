# The order of an étale group of multiplicative type

This module gives the forward implication of
`Langlands.GroupScheme.EtaleMultiplicativeTypeOrderStatement`. For every field
`k`, characteristic exponent `p`, separable closure `Ks`, and affine étale group
scheme `G` over `k`, the theorem `EtaleMultiplicativeTypeOrder.forward` shows that
`IsMultiplicativeType G` implies commutativity and that the cardinality of
`G(Ks)` is coprime to `p`. It does not prove the converse.

The helpers are internal derivations from the published multiplicative-type
geometry and separable-closure splitting theorems, together with Mathlib's
étale-algebra finiteness, Frobenius injectivity, and Cauchy theorem. Their
mathematical motivation is the forward direction of the corrected last
sentence of Milne, *Algebraic Groups* (2017), Example 12.28, as documented in the
unchanged target statement's Markdown. The proof follows a pointwise route
instead of the coordinate-dimension route suggested there.

`coordinate_etale` transports the étale property across the canonical affine
coordinate presentation. `isFinite_of_affine_etale` uses finite-dimensionality
of that coordinate algebra to prove that the structure morphism is finite.
`finite_points` uses that an étale algebra over a
field is finite-dimensional and that there are finitely many algebra
homomorphisms from a finite-dimensional algebra to a field. It injects scheme
points into that finite set using the affine point equivalence.

For `diagonalizable_points_pow_eq_one`, a point of a diagonalizable group is a
homomorphism from its character group to units in the global sections of the
base field's spectrum. Evaluation of global sections and the injectivity of
Frobenius in a field show that a point whose `p`-th power is one is itself one.
This also covers exponent one. `points_pow_eq_one` transports this fact through
base change and a diagonalization over `Ks`.

Finally, `forward` obtains commutativity from
`IsMultiplicativeType.isCommMonObj`. In positive characteristic, if `p` divided
the finite point group's order, Cauchy's theorem would produce an element of
order `p`, contradicting `points_pow_eq_one`. In characteristic zero,
coprimality to the characteristic exponent one holds directly.
