# Canonical weight maps and excluded weights of relative root representatives

For an affine group over any field and an affine representative `j : U ⟶ G`
of the actual root functor, `subgroupActionWeightMap` is the canonical linear
map from a character weight space of `subgroupAction i a j hj` to the ambient
adjoint weight space `weightSpace i χ`. Its underlying map is exactly
`Lie.targetMapLinear j k`, as recorded by `subgroupActionWeightMap_coe`.
Equivariance of the representing inclusion carries an intrinsic weight into
the corresponding conjugation weight, which is the adjoint weight space.
The map is injective by `subgroupActionWeightMap_injective`, since actual
representability includes monomorphy of the inclusion. This construction
requires neither a split torus, local finite type, smoothness, connectedness,
nor a Lie-image hypothesis.

The exclusion results in this internal supporting unit also work over every
field and universe. For those results the ambient
group is affine and locally of finite type, the acting commutative group is a
split torus, and its homomorphism into the ambient group is arbitrary.
Connectedness, reductivity, maximality and actual-root occurrence are not
required. Every positive integral multiple remains in `positiveWeightSpan`.

`disjoint_weightSpace_positiveWeightSpan` says that the ambient weight space
for a character outside all positive multiples of `a` is disjoint from the
full positive cyclic span. The published split-torus decomposition makes the
family of intrinsic action weights supremum independent. For conjugation
these are the published adjoint weight spaces. Every summand of the positive
span belongs to the supremum of weights distinct from the excluded character,
so independence gives the asserted disjointness.

`notMem_actionWeightSupport_subgroup_of_hasLieImage` assumes the exact full
positive Lie image of the actual root functor. A putative support vector lies
both in the excluded ambient weight space and in that positive span. The
preceding disjointness forces it to vanish, contradicting the nonzero vector
required by the actual all-coefficient support definition.

For any affine representative `j : U ⟶ G` of this root functor,
`subgroupAction_weightSpace_eq_bot_of_hasLieImage` transfers the exclusion
to its intrinsic action weight space. The action is the existing
`subgroupAction`, constructed from stability of the root functor and
representability on every scheme test. The published tangent-weight transport
theorem reflects weights through the monomorphic inclusion, so an excluded
ambient support character has zero source weight space.

`subgroupAction_zero_weightSpace_eq_bot_of_hasLieImage` specializes this to
the zero character when `a` is nonzero. The published
`IsSplitTorus.nsmul_ne_zero` shows that every positive multiple of `a` is
nonzero. No smoothness or connectedness of `U` is assumed.

The provenance is internal: these are consequences of the existing actual
weight decomposition, positive Lie-image predicate, represented action,
weight transport and character-lattice torsion-freeness results. This unit
retains the full positive Lie-image equality as an explicit premise. It
does not prove that equality, representability, unipotence, split
unipotence, or the unconditional `RootSubgroupRealizationStatement`.
