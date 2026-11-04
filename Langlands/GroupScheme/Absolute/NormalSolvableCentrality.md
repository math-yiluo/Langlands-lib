# Normal solvable subgroups are central

This module is an internal prerequisite for the positive-root uniqueness proof.
It constructs an actual closed embedding of a triangular diagonal kernel into
its concrete unitriangular group, proves unipotence of that kernel, and derives
centrality of smooth connected normal solvable subgroups over algebraically
closed fields. It does not prove the positive-root uniqueness statement or
assert that these subgroups are tori.

## Actual kernel embedding

Fix a field `k : Type u`, group schemes `G,H` over `Spec k`, a homomorphism
`i : H ⟶ G`, and compatible representation data
`Q : SolvableSubgroupTriangularRepresentation i`. No smoothness, connectedness,
or algebraic-closedness assumptions are needed in this part. The concrete
triangular projection uses the strictly decreasing weights
`j ↦ -(j.val : ℤ)` on `Fin Q.dimension`.

`closed_diagonalKernel` proves that the scheme-theoretic kernel inclusion
`kernelι Q.diagonalHom` is a closed subgroup of `H`: the diagonal target is
an affine closed subgroup of the affine general linear group, so its identity
section is closed, and the kernel is its pullback.

`diagonalKernelMap` is the morphism from this kernel to the kernel of the
concrete block-limit homomorphism. The pullback lift uses the original
triangular embedding on its first component and the kernel's second projection
on its second component. `diagonalKernelMap_comp` records its exact composite
with the target kernel inclusion.

`diagonalKernelEmbedding` composes that lift with the inverse of
`GeneralLinear.blockUnipotentIsoKernel`. The result is an actual group-scheme
homomorphism into the concrete unitriangular group.
`closed_diagonalKernelEmbedding` proves closedness: the composite of the kernel
map with the target kernel inclusion is the composite of two closed
immersions, so the kernel map is closed; composing with the kernel isomorphism
preserves closedness.

`isUnipotent_diagonalKernel` applies the published `unitriangularUnipotent`
and `unipotentClosedSubgroup` results. Affineness and finite type of the
unitriangular ambient group follow from its closed embedding into the smooth
affine general linear group. This establishes unipotence without claiming
smoothness or connectedness of the diagonal kernel.

## Commutator envelope and centrality

`SolvableSubgroupTriangularRepresentation.isCentral_of_normal_of_trivialRadical`
assumes that both `G` and `H` are smooth connected affine, that `i` is closed
and its all-test range functor is normal, and that `G` has trivial ground-field
unipotent radical. The compatible faithful triangular representation `Q` is
an explicit input. The field is arbitrary in this theorem.

The proof constructs the actual action of `G` on `H` by ambient conjugation.
The imported diagonal-invariance theorem and `Q.commutatorKernelFactor` factor
the universal commutator `commutatorMap (𝟙 G) i` through the closed composite
`kernelι Q.diagonalHom ≫ i`. The published `normalCommutator` construction
provides a smooth geometrically connected normal closed envelope `D` of that
commutator. Its minimality gives an actual homomorphism from `D` to the
diagonal kernel, with the prescribed composite into `G`. This homomorphism is
closed because its composite is the envelope's closed inclusion. The diagonal
kernel is affine of finite type, being closed in the smooth affine `H`.
Closed-subgroup inheritance therefore makes `D` unipotent.

Triviality of the ambient unipotent radical now makes the full range functor
of `D` trivial. On an arbitrary test scheme the factor of the commutator
therefore has identity image. The group commutator identity gives commutation
of every ambient point with every subgroup point. Applying this to every
restriction of a subgroup point proves `IsCentral i` for the existing
scheme-theoretic centre functor, including nonreduced and nonaffine tests.

`IsSolvableGroupScheme.isCentral_of_normal_of_isPseudoReductive` assumes an
algebraically closed field, smooth connected affine `H`, solvability of `H`,
pseudo-reductivity of `G`, and a normal closed inclusion `i`. It constructs `Q`
using the published ambient faithful representation and Lie–Kolchin
triangularization, then applies the preceding theorem. The connected
reductive specialization
`IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive` uses the
published implication from connected reductivity to pseudo-reductivity. There
is no torusness premise or characteristic restriction.

## Provenance and scope

This is internal derived content. The kernel construction follows the
pullback-and-unitriangular method already used in
`Absolute.SolvableTorusQuotientReduction`, without importing its conditional
kernel-geometry interface. The centrality argument combines the actual
compatible triangular representation and universal diagonal-invariance
results with the existing smooth connected normal commutator-envelope
construction, unitriangular unipotence, closed-subgroup inheritance, and the
definition of trivial unipotent radical. It uses no Lie-algebra equality to
identify subgroup schemes and no smoothness or connectedness assertion about
the full diagonal kernel. The exact rank-one positive-root theorem remains a
separate obligation.
