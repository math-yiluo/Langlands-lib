# Opposite factor pairs from a rank-one open cell

This internal construction derives actual opposite factor pairs from the
published `RankOneRootCellRelation.WeylData`. It uses no additional geometric
existence premise beyond those data and no restriction on the field or its
characteristic. It does not yet construct such data for every ambient root or
prove pinned automorphism rigidity.

`WeylData.scalePositive` rescales the positive additive parametrization by any
unit in the base scheme's ring of global functions. Rescaling preserves its
character equivariance and changes the triple-cell map by an automorphism of
its source. Applying the published `WeylData.inCell_A_one_mul_N` to these
rescaled data proves `inCell_A_unit_mul_N`: every unit base root coordinate,
multiplied by the Weyl point, lies in the original open cell. The rescaling
isomorphism and its coordinate equation are imported from
`Reductive.SplitRankOneRootCellProof`.

`comp_mem_rootSubgroup` supplies actual root-subgroup membership for any
character-equivariant additive parametrization, on every test scheme. Its
extension multiplies the affine-line coordinate by the pulled-back additive
coordinate and then applies the parametrization. It evaluates to the identity
at zero and recovers the torus orbit on the multiplicative group. Thus it
satisfies the defining conditions of `RelativeRoot.subgroup` directly.

Assuming the torus inclusion is a monomorphism,
`WeylData.exists_oppositeFactorPair` applies the open-cell factorization to
write `x n = b t a`. It chooses the opposite factors `b⁻¹` and `n a⁻¹ n⁻¹`.
Equivariance gives membership of `a` and `b` in the positive and negative actual
root subgroups. The Weyl point acts by the supplied lattice reflection, which
sends the root to its negative; the published normalizer conjugation theorem
therefore puts the second factor in the negative root subgroup as well.
The product with `x` is `t n⁻¹`, a normalizer point because torus points
centralize the torus. These are precisely the three conditions in
`RelativeRoot.IsOppositeFactorPair`.

The provenance is an internal algebraic consequence of the imported root-cell,
reflection, and all-test root-subgroup interfaces. No original-literature
statement is newly formalized in this unit.
