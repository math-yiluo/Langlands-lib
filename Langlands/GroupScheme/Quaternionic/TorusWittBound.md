# Split-torus rank bounds from the division-algebra Witt index

Author: Worker 118.

Over an infinite field `K`, let `D` be a finite-dimensional division
`K`-algebra with a first-kind involution and let `H` be any square matrix
over `D`. If its division-algebra Witt index is at most one, the actual
unitary isometry group has split rank at most one. The same conclusion
holds for every group scheme with a monomorphism into this isometry
group, in particular for the reduced-norm-one symplectic subgroup when
the centrality and nonempty-index hypotheses for its definition hold.

`torusInverseUnitMatrices` records the original inverse unit matrices at
the base-field points of a supplied standard split-torus homomorphism.

The proof restricts the faithful inverse-right-regular representation of
the matrix-algebra unit group to a supplied faithful standard split
torus. If its rank is at least two, the universal weight-pair construction
gives two nonzero coefficient columns with nonzero, distinct and
nonopposite integral weights. The original-algebra coefficient
construction gives two nonzero matrices. Their rows are common
eigenvectors for the inverse unit matrices; a nonzero matrix has at least
one nonzero row, so each common weight space is nonzero as a left
`D`-subspace.

The affine isometry-cut comparison in the companion module establishes
the isometry equation for these inverse matrices. Over the infinite
field, monomial characters on tuples of units distinguish integral
exponents, and a nonzero exponent is nontrivial somewhere. The two
nonzero weights have nonzero doubles, and their sum is nonzero since
they are not opposite. Thus each common weight space is totally
isotropic and the two spaces are mutually orthogonal. Distinct weights
make them disjoint. The existing division-algebra dimension argument
then forces Witt index at least two, a contradiction.

Consequently every closed standard split torus has dimension at most
one. The definition of split rank as a supremum gives the asserted upper
bound. A monomorphism into the unitary group preserves faithfulness of
each torus; the symplectic case uses its actual kernel inclusion.

This is an internal consequence of the published representation,
coefficient, exponent-separation and isometry-weight interfaces. No
nondegeneracy, antihermitian condition, quaternionic dimension, local
field hypothesis or characteristic restriction is used. Infinitude of
`K` is an explicit hypothesis. The module proves only an upper bound;
the rank-one lower bound and the structural conclusions of the local
symplectic target remain separate obligations.
