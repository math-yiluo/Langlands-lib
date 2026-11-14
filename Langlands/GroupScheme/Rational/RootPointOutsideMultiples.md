# Actual root points outside higher-multiple root groups

This derived unit concerns the intrinsic all-test relative root subgroup functors
of a smooth affine group over a field, acted on by a split torus. The torus map
need not be monomorphic or maximal, and neither reductivity nor connectedness of
the ambient group is required. All declarations have arbitrary universe.

An actual relative root `a` has a nonzero ambient `a` weight space. The exact
cyclic tangent image in `RootSubgroupLieImage`, combined with the intrinsic
split-torus support formula in `SemigroupWeightSupport`, puts `a` in the tangent
weight support of its root functor. If `a` is excluded from the positive cyclic
tail of a nonzero character `b`, it is absent from the support of the `b` root
functor. Monotonicity of tangent support therefore prevents all-test containment
of the `a` root functor in the `b` root functor.

Over an algebraically closed field this failure has an actual rational-point
witness. Choose smooth closed representatives using
`RootSubgroupRepresentability`. The source is reduced by
`SmoothReducedProof.isReduced_of_smooth_over_field` and locally of finite type
by smoothness. If every source-root rational point belonged to the target root
functor, `SubgroupFunctor.range_le_of_algClosed_points` would give all-test
containment in the closed target representative, contradicting the support
argument. This proves `exists_rootPoint_not_mem_of_not_mem_cyclicTail`.

For a nonzero split-torus character, natural multiples are distinct by
`IsSplitTorus.nsmul_character_injective`. Consequently `a` cannot be a positive
multiple of `n • a` when `2 ≤ n`. The specialization
`exists_rootPoint_not_mem_nsmul` gives a point of the actual `a` root functor
outside the actual `n • a` root functor over an algebraically closed field.
`rootPointOutsideMultiple` chooses this point with both membership and exclusion
in its subtype. The chosen point is nonidentity because every subgroup contains
the identity. The all-test noncontainment conclusion does not require the field
to be algebraically closed.

The provenance is the composition of the named Library interfaces and elementary
character arithmetic. No separate original-literature claim is made. This unit
does not identify a root's affine depth or prove survival in the reductive
quotient of a facet model. In particular, a nonidentity root point alone would
not establish exclusion from the doubled-root subgroup; the exact tangent weight
and rational-point containment argument supply that stronger conclusion here.
