# Recognizing Borel subgroups by the absence of opposite weights

This internal helper for the Borel-locus proof is derived from
published Library theorems, with no additional literature assertion.

For affine group schemes over a ring, a monomorphic inclusion reflects every
character weight space on the actual dual-number Lie kernel. The theorem
`weightSpace_ne_bot_iff_exists_lieKernel_image` expresses this as an equivalence
between a nonzero intrinsic weight space and a nonzero ambient weight vector
in the image of the subgroup Lie algebra.

For a connected reductive group `G` over a field, and a split maximal torus
factoring as `f : T → P` followed by `i : P → G`,
`IsBorelSubgroup.no_opposite_weights` says that Borelness of `i` forces at
least one of `weightSpace f α` and `weightSpace f (-α)` to vanish for every
nonzero character `α`. It transports nonzero intrinsic weight vectors to the
ambient Lie algebra and applies the published `rankOneSolvableObstruction`.

Over an algebraically closed field, when `i` is parabolic,
`isBorelSubgroup_iff_no_opposite_weights` proves the converse as well. First
realize the geometric Borel witness over the original field. Its presence
implies connectedness of `P`. The construction
`BorelExistence.borelPairInOvergroupData`, supplied with the published
`borelConjugacy`, chooses an ambient Borel inside `P` through the specified
torus. The third clause of `regularCocharacterBorel` represents that Borel
as a dynamic parabolic of a regular cocharacter. The no-opposite condition
gives exactly the Lie-image obstruction required by
`isIso_of_comp_eq_of_isRepresentedBy_parabolic`, using the published
`dynamicLie`, `dynamicSmooth`, `lieSubgroupEquality`, and
`relativeRootNegation`. The chosen Borel is therefore isomorphic to `P`,
and Borelness transports along this isomorphism.

The torus need not be in standard coordinates. Affineness of `P` and `G`
is explicit in these helper declarations; in the intended application it
follows from the closed parabolic inclusion and reductivity of `G`.

The corollary `isBorelSubgroup_iff_no_opposite_weight_finranks` uses smoothness
of `P` to make its Lie algebra and weight subspaces finite dimensional.
`Submodule.finrank_eq_zero` then converts vanishing of a weight space into
vanishing of its dimension.

For a standard split torus,
`splitTorus.isBorelSubgroup_iff_no_opposite_exponent_weight_finranks` transports
the quantifier over characters through the additive equivalence
`splitTorus.characterLatticeEquiv k I`. This equivalence preserves zero and
negation, so the criterion becomes: for every nonzero `m : I → ℤ`, the weight
dimension indexed by `m` or the weight dimension indexed by `-m` is zero.
