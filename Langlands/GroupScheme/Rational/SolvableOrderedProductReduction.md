# Exact solvable ordered products from narrower structural inputs

This internal construction is conditional. It retains three structural
propositions: `SolvableMaximalTorusSemidirectStatement`,
`Torus.SolvableFixedContainmentConnectedStatement` and
`CentralStableVectorSubgroupStatement`. None is proved here, and the
unconditional host theorem remains open.

`hasOrderedSemigroupProducts_semidirect_of_solvable` concerns an actual action
of a smooth connected affine group `K` on a smooth connected affine group
`G`, together with a commuting split-torus action on `G`. Uniform all-test
solvability is required only of `G`. The solvable-source inverse-image theorem
supplies the exact semigroup comparison along the closed normal inclusion
into the actual semidirect product, for every additive semigroup. Its
connectedness premise is precisely the retained solvable fixed-containment
criterion. Published functoriality and the local-comparison semidirect
assembly then transfer the exact ordered-product property from `G`.

`hasOrderedSemigroupProducts_of_solvable_subgroup_factorization` starts with
two actual subgroup inclusions and an isomorphism given by their actual
normal-factor-first multiplication. The ambient action preserves the normal
range and fixes the acting range pointwise on every scheme test. The
normal range is normalized by the acting range. The actual represented
normal action commutes with normalized conjugation. The preceding semidirect
result applies, and the equivariant group-scheme factor isomorphism transports
the exact factors and original ordered multiplication back to the ambient
group. The normal factor is assumed uniformly solvable. The acting factor
need not be solvable.

`semigroupOrderedProduct_of_solvableStructuralInputs` has exactly the three
structural premises displayed above and concludes the existing arbitrary
universe `SemigroupOrderedProductStatement`. Scalar descent reduces the
assertion to algebraically closed fields in the same universe. For an
arbitrary smooth connected affine solvable group and split-torus action,
`solvableFactorization` supplies actual compatible factors from the retained
maximal-torus decomposition: a smooth connected affine unipotent normal
factor and a smooth connected affine fixed torus, with original closed
inclusions and actual multiplication isomorphism. The normal factor inherits
the ambient uniform derived-series bound through its monomorphic original
inclusion. No separate assertion that every unipotent group is uniformly
solvable is needed.

The narrowed central-vector induction gives ordered products of the normal
factor, retaining only the connectedness and central-vector premises.
The specialized subgroup-factorization result then gives the algebraically
closed ambient assertion, and the existing scalar descent returns the
original-field assertion.

`solvableOrderedSemigroupProduct` chooses the supplied smooth connected closed
factors and records the actual ordered multiplication as an isomorphism over
the original field. Its result is the existing
`OrderedSemigroupProductData b Ψ`. The constructor retains all three
structural arguments explicitly.

All fields, universes and original finite block orders are covered, including
`Fin 0`. The support is the complete occurring Lie-weight support, retaining
zero whenever it occurs. Generation is positive
`AddSubsemigroup.closure`; zero is not adjoined. Cross-exclusion is exactly
`Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s))` for distinct indices,
alongside the original block disjointness. There is no disjointness assumption
on two generated closures.

The provenance is internal: this unit composes the actual solvable-factor
construction, solvable-source semigroup intersection, local semidirect
assembly, equivariant factor transport, central-vector induction and scalar
descent. The adapted induction is joint work of Worker 1313 and Worker 362.
This unit narrows the earlier reduction's full semigroup-intersection premise
to its independent solvable fixed-containment connectedness input. It does
not establish the remaining structural propositions or complete the host
proof task.
