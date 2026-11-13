# Isotropic subspaces from generating Hermitian weights

This internal linear algebra construction supports the upper comparison between
split-torus rank and isotropic dimension. Its input is a basis of a vector space,
an integral weight for each basis vector, generation of the full integral
lattice by those weights, and vanishing of the sesquilinear pairing between
basis vectors whose weights do not sum to zero.

`exists_nonopposite_subfamily` selects a maximal finite subfamily containing
no pair whose sum is zero, including pairs consisting of the same element.
Every nonzero weight is equal or opposite to a selected weight: an uncovered
weight could otherwise be inserted. The integral lattice is torsion free,
so twice a nonzero weight is nonzero, as needed when inserting that weight.

`card_le_of_generators_up_to_sign` proves that any subfamily representing every
weight up to sign has cardinality at least the lattice rank. Its integral span
contains every original weight, hence is the entire lattice; the dimension of
the span of a finite set is bounded by its cardinality.

`selectedWeightSpan` defines the subspace spanned by a finite selected subfamily
of a basis. `exists_isotropic_of_weightBasis` applies this construction to the
selected weights.
The full pairing vanishes on it, by the assumed pairwise orthogonality and
linearity in the first variable and semilinearity in the second. Since these
are distinct members of a basis, the dimension of their span is the number
selected. It is at least the lattice rank.

The results apply to any field, in every characteristic, and to any scalar
endomorphism defining the second-variable semilinearity. Hermitian symmetry
and nondegeneracy are not needed for these particular conclusions. These are
elementary derived lemmas: they use finite maximality and dimension bounds
rather than an external classification theorem. Extracting the weight basis,
proving its orthogonality from a universal isometry equation, and constructing
it from the supplied all-test Hermitian presentation remain separate steps.
