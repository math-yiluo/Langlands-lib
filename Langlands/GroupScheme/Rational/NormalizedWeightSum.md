# Finite sums of actual subgroup tangent weights

This derived auxiliary module constructs the integral sum of the distinct
characters in the actual tangent-weight support of a subgroup functor under
conjugation by a split torus. Each character is counted once, including the zero
character when it occurs. This is not the Lie determinant character: weight-space
dimensions are not used as multiplicities.

The field and its universe are arbitrary. The ambient group scheme `G` is affine
and locally of finite type. A split commutative group scheme `T` maps to `G` by
any group-scheme morphism `i`, and `F` is any all-test subgroup functor of `G`.
No representability, smoothness, connectedness, reductivity, maximality, or
normalization is needed for the sum.

`IsSplitTorus.finite_actionWeightSupport` embeds this support in the published
finite support of the ambient adjoint weight spaces. An occurring weight has a
nonzero vector in its ambient weight space, so that space cannot be bottom.
`actionWeightSupportFintypeOfIsSplitTorus` provides a finite enumeration of the
unchanged support subtype. `actionWeightSum` sums its underlying characters in
the existing integral character lattice.

`latticePairing_actionWeightSum` follows from linearity of the existing integral
character/cocharacter pairing. If the support is nonempty and every occurring
character has strictly positive pairing with a specified cocharacter, the finite
sum has strictly positive pairing, by `Finset.sum_pos`. Consequently the sum is
nonzero. These hypotheses are explicit in
`latticePairing_actionWeightSum_pos` and `actionWeightSum_ne_zero_of_pos`;
positivity and nonemptiness are not asserted for arbitrary subgroups.

For invariance, let `j : H → G` be any group-scheme morphism and let `t : T → H`
have a monic underlying scheme map. Assume `F` is stable under conjugation along
`j` on every test scheme. The existing `normalizedWeightPermutation` restricts
the actual character action of `relativeWeylGroup t = N_H(T)(k)/Z_H(T)(k)` to
this support. Applying `Fintype.sum_equiv` to this permutation proves
`relativeWeylCharacterAction_actionWeightSum`: the quotient fixes the integral
support sum. The quotient itself need not be finite.

The provenance is the actual tangent-support definition, the finite-dimensional
split-torus weight decomposition, the normalizer permutation, and elementary
finite-sum algebra. The module supplies a finite character sum usable in the
minimal-parabolic Levi-centralizer argument. It does not prove geometric Weyl
realization, Galois stability, positive-root containment, or the main structural
theorem.
