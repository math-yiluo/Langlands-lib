# Transporting the torus property to a supplied cocenter

Author: Worker 1282.

This is a derived interface and conditional reduction built from the published
`CocenterQuotientExistenceStatement`, actual fppf quotient comparison, and the
proved finite Galois splitting theorem for field tori. It is not a numbered
result transcribed from literature.

`SuppliedCocenterTorusStatement.{u}` says that, over every field `k : Type u`,
every commutative fppf quotient `q : M → Q` by a supplied actual derived subgroup
`d : D → M` of a connected reductive group `M` has torus target `Q`. The statement
quantifies over every such quotient. No affineness, finite type, smoothness or
torus hypothesis is imposed on `Q`.

`suppliedCocenterTorus_of_existence` proves this statement under the explicit
premise `CocenterQuotientExistenceStatement.{u}`. The existence input supplies a
torus quotient `q₀ : M → Q₀` with the same full scheme-theoretic kernel as `q`.
The affine source `M` is quasi-compact, and every group scheme over a field is
separated by `fieldSeparated`. Hence both quotient morphisms are quasi-compact.
`FppfQuotientComparison.iso` then constructs the isomorphism `Q ≅ Q₀`.
`IsTorus.of_iso` transports the torus property across that isomorphism.

`suppliedCocenter_finiteGaloisSplitting_of_existence` applies the unconditional
`torusFiniteGaloisSplitting` to this result. It provides a field `E : Type u`,
an algebra structure over `k`, finite dimensionality, the Galois property, and
splitness of the actual base change of the supplied quotient.

The existence premise remains unproved in this module. These reductions do not
establish that a split-torus centralizer is connected reductive, identify its
cocenter characters with a root-theoretic annihilator, or construct a basis
permuted by Galois. In particular they do not prove that the cocenter is induced.
