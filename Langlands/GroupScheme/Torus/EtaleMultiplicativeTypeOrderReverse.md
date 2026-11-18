# Diagonalizing an étale group using its characters

This internal helper assembles the geometric converse route for
`EtaleMultiplicativeTypeOrderStatement`. It works over a separably closed field
`K`, with characteristic exponent `p`, and a finite étale commutative group
scheme `G` whose rational point count is coprime to `p`.

`exists_diagonalizableIso_of_liftable_characters` assumes that every abstract
homomorphism `G(K) → Kˣ` lifts to a morphism from `G` to the actual multiplicative
group scheme that respects multiplication. Under this explicit premise, it
produces an isomorphism from `G` to an actual diagonalizable group with finitely
generated character group. This first lemma keeps the lifting premise explicit.

The proof takes a finite separating family of abstract characters from
`PrimeToCharacteristicCharacters.exists_separating_family`, lifts them using
the premise, and bundles their natural maps on all test schemes into actual
group-scheme homomorphisms. Their product gives a morphism from `G` to a split
torus indexed by the finite set `G(K)`. The selected characters show that the
map on rational points is injective. The pointwise closed-immersion criterion
over a separably closed field makes it a closed subgroup, and the published
closed-subgroup presentation theorem for split tori supplies diagonalization.

`exists_diagonalizableIso_of_coprime_order` then discharges the lifting premise
using `Cartier.exists_gm_hom_of_points_of_isSepClosed`. Thus its conclusion
requires only the finite étale hypotheses, commutativity, separable closedness,
and the stated coprimality of the point count.

This is a derived proof assembly for the corrected last sentence of Milne,
*Algebraic Groups* (2017), Example 12.28. It follows the character-embedding
route rather than constructing a Fourier isomorphism of coordinate algebras.
