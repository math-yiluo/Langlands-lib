# Finite induced-cuspidal embedding assembly

Worker 1570. This internal construction isolates the finite-sum and kernel
argument of Renard VI.7.2, printed pp.182–183 / PDF pp.188–189, from the
still-needed cuspidal projection theorem for the actual Levis. It does not
prove the closed rational embedding statement.

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
version 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source chooses the cuspidal part of each Jacquet module and uses the
faithful exact left adjoint R to prove the adjunction unit injective. The
implemented route uses the same orbit maps but argues on their actual kernel.

`finiteInducedJacquetMap` adds the actual first-adjointness maps into the
actual `SmoothRep.directSum`. The index `Finset κ` is finite. The source has
carrier `Type uV`; each inducing and target carrier has
`Type (max uI uG uV)`. The first-adjointness construction uses the full
normalized smooth function-space induction model and the inverse-half-modulus
Jacquet action. Closedness and unimodularity of each radical are explicit.
The component lemma identifies each projection with exactly its orbit map.

`CuspidalJacquetProjectionTarget` is an internal objectwise prerequisite.
For each source it asks for cuspidal Levi objects and actual maps from the
Jacquet modules, such that postcomposition kills no nonzero map from any
cuspidal object. A projection onto a cuspidal direct factor has this property
when its complementary factor admits no such map. This proposition does not
assert that those projections exist, and is not a new premise of the published
rational statement.

`finiteCuspidalInducedEmbedding_of_projections` assumes that objectwise input,
compact-limit radicals, and minimal nonzero cuspidal-Jacquet detection. It
forms the kernel K of the finite orbit map. If K were nonzero, detection
would give a nonzero cuspidal Jacquet module of K. Finite averaging makes its
map into the Jacquet module of the source injective. Each orbit component
vanishes on K; evaluating at the identity says that the projection kills
this injective map. The projection property forces that map to be zero,
contradicting the nonzero source. Thus K is zero and the finite orbit map is
injective. No exactness of induction or supplied faithful I/R unit is used.

All maps and kernels are the existing complex-linear equivariant models.
The conclusion is the unchanged `FiniteCuspidalInducedEmbeddingTarget`.
The universal rational theorem still requires proving or importing the
projection prerequisite at its original structural telescope. No admissibility,
length, dimension, finite generation or irreducibility premise is added.
