# Nonidentity actual root points from realization and vector structure

This internal conditional deduction uses the existing actual subgroup functors
and their dual-number Lie images. It does not prove the geometric
`RootSubgroupRealizationStatement`, `RootSubgroupVectorStatement`, or the
relative-root-system target.

A vector group of positive dimension has a nonidentity rational point:
choose the constant vector of global sections equal to one in the coordinates
at `Spec k`. One coordinate differs from zero because `k` is a field. If a
represented vector group has a nonzero exact Lie image, its dimension is
positive. Indeed, dimension zero makes its points subsingleton on every test
scheme, including the dual-number test, forcing every vector in that Lie image
to be zero. The representative monomorphism preserves nonidentity.

For an actual root `a`, the nonzero `a`-weight space is contained in
`positiveWeightSpan i a`, using the first positive integral multiple.
The realization and vector targets therefore yield a nonidentity rational
point in `U_a` whenever `2a` is absent. When `2a` is a root, the published
crystallographic root-line bound rules out `4a`. Apply the same argument to
`2a` and use the vector target's all-test inclusion `U_(2a) ≤ U_a`.
No point-surjectivity of an fppf quotient is used.

`RelativeRoot.exists_rootPoint_of_statements` retains the two global structural
targets and `HasRelativeRootSystem i` as explicit hypotheses, along with
connected reductivity, maximal splitness of the actual torus, and the
affineness and monicity instances required by the existing constructions.
The field and universe are arbitrary; nonreduced roots and the empty-root
case are included.

`RelativeSimpleRootPointData.of_rootSubgroup_statements` chooses these points
for all actual simple roots, supplying the input data of the already defined
relative Tits nondegeneracy reduction. The full Tits-system statement remains
unproved.

The proof route is an internal deduction from the published definitions and
`HasRelativeRootSystem.nsmul_not_mem_of_three_le`; it is not presented as
a new translation of a literature theorem. Worker 1285 suggested the
zero-dimensional-vector contradiction and identified the existing root-line
helper; Worker 1288 implemented the deduction.
