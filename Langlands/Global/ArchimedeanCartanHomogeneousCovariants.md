# Actual homogeneous invariant coefficients and compact covariants

Author: Worker 94. This internal construction specializes the canonical
projections in `SymmetricAlgebraHomogeneous` and `SymmetricTensorHomogeneous`
to the actual algebras and covariants in `ArchimedeanCartanCovariantFiniteness`.
It retains an arbitrary field `K : Type u` and every natural rank.

`lieSymmetricComponent` and `cartanSymmetricComponent` are the actual canonical
degree projections on the whole and complementary symmetric algebras. Naturality
for linear induced maps shows that they commute with the actual Cartan inclusion
and projection, full-group conjugation on the whole algebra, and full compact
conjugation on the complementary algebra. Their restrictions
`lieSymmetricGroupInvariantComponent` and
`cartanSymmetricCompactInvariantComponent` are complex linear maps on the
actual fixed subalgebras. Cartan restriction commutes with these maps. Each
full-group invariant component is homogeneous in its indicated degree.

`cartanSymmetricTensorComponent` tensors the complementary degree projection
with the identity on the vector space underlying `τ : ContinuousCompactRep`.
It commutes with the actual diagonal action of every element of the full
standard compact subgroup. Consequently it restricts to a complex linear map
`cartanSymmetricCovariantComponent` on the actual fixed tensors.
`IsHomogeneousCartanCovariant` means that the canonical tensor projection
fixes the tensor. The degree components are homogeneous, satisfy the Kronecker
projection identities, and give a finite decomposition of every covariant,
with all higher components zero.

For a full-group invariant coefficient `P` and a covariant `x` homogeneous
of degree `e`, projection of `P • x` onto degree `d` is zero when `e > d`.
When `e ≤ d`, it is the degree `d-e` full-group invariant component of `P`
acting on `x`. The action is the published coefficient action by actual
Cartan restriction. The proof applies the tensor coefficient-selection identity,
then commutes degree projection with the actual Cartan symmetric projection.

All maps and identities here are algebraic and do not need the number-field
assumption used in the imported finite-generation theorem. This module does
not yet select finite homogeneous generators, transfer to the enveloping
center, or prove automorphic differential growth.
