# Actual Hermitian weight pairing and coordinate planes

This internal derivation starts with `TypeAHermitianTorusCoordinates L d e`:
a nonsingular Hermitian form over the separable quadratic extension `L/K`,
an actual all-test presentation of `G`, and the supplied characters of the
original split torus. It adds no characteristic restriction.

`gram_eq_zero_of_weight_sum_ne` proves that a nonzero Gram entry pairs only
opposite integer weights of any cocharacter of that split torus. The proof
evaluates the Gram-preservation identity on the generic Laurent point of the
cocharacter. The coefficient involution fixes the diagonal torus entries.
Projection to cover coefficients gives equality of Laurent monomials, and
uniqueness of the exponent of a nonzero monomial forces the weight sum to
vanish. This uses the published Laurent-point and tensor-projection lemmas.

`coordinatePairMap` inserts a vector with two coordinates into two specified
positions. `coordinatePairSubspace` is its range. Distinct positions give an
injective map and hence dimension two. A zero Gram block on those positions
makes the subspace totally isotropic, as is checked on the actual Gram
pairing by expanding the two coordinate sums.

Consequently `two_le_splitRank_of_positive_pair` proves that two distinct
coordinates with strictly positive weights for the same cocharacter force
split rank at least two. All four Gram entries in their block vanish by the
weight-sum lemma. The published presentation theorem bounds the dimension of
this totally isotropic coordinate subspace by the actual split rank.

These are derived auxiliary constructions, with no new literature claim. No
division by two occurs. The exact distinguished vertices and the full local
rank-one enumeration remain to be proved.
