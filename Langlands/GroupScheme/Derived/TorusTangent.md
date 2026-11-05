# Nonzero torus weights in the actual derived tangent

Authors: Worker 1667, with the tangent-spanning route proposed by Worker 1447.

This internal helper works over every field `k : Type u`. The ambient group
scheme `G` is affine and smooth. A commutative group scheme `T`, an actual
homomorphism `i : T.toGrp → G`, and a proof that `T` is split are supplied.
The torus map need not be a closed immersion or maximal. Reductivity and
characteristic assumptions are unnecessary for these implications.

`RelativeRoot.weightSpace_le_tangentSubmodule_derivedSubgroup` puts every
nonzero adjoint character weight space inside the actual dual-number tangent
submodule of `derivedSubgroup G`. It composes two published results:
`RelativeRoot.weightSpace_le_tangentSubmodule_subgroup` puts that weight
space in its intrinsic root functor's tangent, and
`RelativeRoot.subgroup_le_derivedSubgroup` puts the whole root functor in the
derived subgroup on every test scheme. Monotonicity of tangent submodules
gives the conclusion. The root functor retains the Library's existing
positive-integral-multiple convention.

`RelativeRoot.tangentSubmodule_derivedSubgroup_sup_torus_eq_top` retains an
explicit assumption that the zero adjoint weight lies in the tangent
submodule of the torus range. The actual split-torus action weight spaces
span the ambient Lie module. The preceding lemma treats every nonzero
character, and the explicit assumption treats zero, so the derived tangent
and torus tangent have sum equal to the full Lie module.

For a supplied actual derived inclusion `d : D → G`,
`IsDerivedSubgroup.weightSpace_le_tangentSubmodule_range` and
`IsDerivedSubgroup.tangentSubmodule_range_sup_torus_eq_top` rewrite those
two conclusions using the full actual range of `d`.
`IsDerivedSubgroup.tangentSubmodule_range_sup_selfCentralizing_torus_eq_top`
derives the zero-weight containment from the explicitly supplied all-test
equality `torusCentralizer i = SubgroupFunctor.range i`. A zero-weight
infinitesimal point belongs to the torus centralizer by the published
`Lie.mem_torusCentralizer_of_mem_weightSpace_zero`, and that equality puts
it in the torus itself.

When `D` is affine as well,
`IsDerivedSubgroup.weightSpace_le_range_targetMapLinear` identifies the
derived tangent with the range of the actual linear map on dual-number
identity kernels. `IsDerivedSubgroup.range_targetMapLinear_sup_torus_eq_top`
gives the corresponding full-sum result, still retaining the zero-weight
assumption. The actual derived inclusion is a closed immersion and therefore
monomorphic, as required by `RelativeRoot.tangentSubmodule_range`.

The provenance is an internal composition of published root, derived,
weight-decomposition, and actual tangent-image results. These lemmas retain
the zero-weight or self-centralization assumption explicitly.
They do not assert surjectivity of subgroup multiplication. Those are
separate obligations in the full derived/maximal-torus product proof.
