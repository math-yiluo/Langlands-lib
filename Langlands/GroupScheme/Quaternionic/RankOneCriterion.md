# Rank one from a Witt upper bound and a nontrivial cocharacter

Author: Worker 118.

Let `K` be an infinite field and `D` a finite-dimensional division
`K`-algebra with a first-kind involution. For a form matrix of Witt
index at most one, every affine group with a monomorphism into its actual
unitary isometry group has split rank exactly one if it admits a
nontrivial base-field cocharacter.

`splitRank_eq_one_of_mono_unitary` combines the proved Witt-index upper
bound with the split-torus-image lower bound from
`Rational.NontrivialCocharacterRank`. The second theorem applies the same
argument to the actual reduced-norm-one symplectic subgroup, under the
centrality and nonempty-index hypotheses for that definition. Its
affineness follows from the affine isometry cut and the kernel
construction.

These are internal conditional consequences. Existence of a nontrivial
cocharacter is retained explicitly, and is not asserted here from an
isotropic vector or Witt index. No characteristic restriction or standard
symplectic structural theorem is used, and neither simple connectedness
nor almost simplicity is claimed.
