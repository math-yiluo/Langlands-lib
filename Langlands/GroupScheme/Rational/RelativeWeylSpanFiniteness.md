# Relative Weyl faithfulness and finiteness from joint spanning

This internal supporting module combines the existing actual quotient
actions, their kernel comparison, and the conditional character-restriction
faithfulness bridge. The field and universe are arbitrary, the ambient group
is affine, and the torus inclusion is a monomorphism.

For a split torus,
`IsSplitTorus.relativeWeylRootPermutation_eq_one_iff` expresses the existing
equality of permutation and rational root-span kernels at an individual
quotient class.

`IsSplitTorus.relativeWeylRootPermutation_injective_of_span` assumes that the
rationalized union of actual roots and restrictions of actual rational group
characters spans the full rational character space. The imported faithfulness
bridge makes the root-span action injective under exactly that premise.
The identity-kernel criterion and equality of the two kernels then make the
permutation action injective.

When the ambient group is locally of finite type,
`IsSplitTorus.finite_relativeWeylGroup_of_span` combines that same root-span
faithfulness bridge with the imported finite-image theorem and its
faithfulness-to-finiteness corollary. Its conclusion is finiteness of the
actual quotient `N(k)/Z(k)`. `relativeWeylGroupFintypeOfSpan` chooses a finite
enumeration of this quotient.

All claims are derived from the imported actual actions and elementary group
arguments. The module assumes the joint-spanning premise and does not prove
it for connected reductive groups. It retains the empty root set and makes
no reducedness or characteristic assumption. The intrinsic complement,
general relative-root pairing, actual reflection existence and generation,
Weyl-image equality, and exact `RelativeRootSystemStatement` remain separate
obligations.
