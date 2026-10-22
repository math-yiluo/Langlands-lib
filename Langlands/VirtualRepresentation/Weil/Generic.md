# Integral lattices of actual continuous irreducible representations

This development uses Worker 17's genuine finite-dimensional representation
category and its quotient by invertible linear intertwiners. The input is a
group `G` with a topology. The coefficient field is the complex numbers with
their usual topology in `FiniteRepresentation.IsContinuous`; the carrier
universe is independent of the group universe. No topological-group hypothesis
is needed merely to construct these types.

`IrreducibleBasis G` is the disjoint union over positive integers `n` of
`FiniteRepresentation.ContinuousIrreducibleClasses G n`. Its entries are
isomorphism classes of actual finite-dimensional continuous irreducible complex
representations of the specified rank, not arbitrary labels. `underlyingClass`
forgets the rank and conditions into the genuine representation quotient.
`IrreducibleLattice G` is the finite integral coefficient module on that basis.
The degree and multiplicity pairing use `Integral`'s actual linear maps.
Degree is integer-valued and permits negative virtual values.

`HasFiniteImageClass` uses an actual finite-image representative of the genuine
isomorphism class; its supported submodule is constructed without identifying
finite image with Galois type or finite-order determinant. `FactorsThrough f`
requires an actual representation of the target group whose pullback along `f`
has the specified isomorphism class. The map and target group are genuine input
objects, with independent target-group universe. This is algebraic factorization:
no target topology, continuity of the factor representation, or surjectivity
of `f` is asserted. `factoringSupported` restricts support to these classes.
Later local applications must supply the actual map to the finite Galois group.

`IsUnitaryClass` says that the underlying isomorphism class has a representative
with an invariant positive-definite Hermitian inner product in the precise
`FiniteRepresentation.IsUnitary` sense. It is a predicate on the quotient
itself, defined by existence of an actual representation and equality of
genuine isomorphism classes. It does not select a representative or form,
and does not assume a separate isomorphism-invariance theorem. The class
already belongs to the continuous irreducible basis. Restricting to this
predicate gives `UnitaryBasis`, its integral coefficient lattice, its supported
submodule in the full lattice, and the concrete equivalence between the two
models. Inclusion and coefficient restriction use Mathlib's actual
finite-support maps. `unitaryDegree` is the composite of inclusion and degree;
`unitaryPairing` is the integral dot product on this specified unitary basis.
The unitary rank stratum has no assumed finiteness.
`unitaryFactoringSupported` further restricts to unitary classes factoring
through the supplied actual group map.

`basisClass` and `unitaryBasisClass` accept actual representations and explicit
proofs of their predicates and specified positive rank. They construct the
quotient and subtype values directly. `ofRepresentation` and
`ofUnitaryRepresentation` then give the corresponding multiplicity-one
generators. The rank equality is a constructor input selecting the stated
rank; no existence or classification statement is hidden in that input.

## Source correspondence

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), section 1.1, p.439, defines the continuous irreducible
complex rank-indexed Weil classes. Sections 2.5-2.6, pp.445-447, form the free
integral group across positive ranks, extend degree, and specify its integral
orthonormal-basis pairing. The unitary restriction used in the construction
comes from the actual unitary representations discussed in sections 2.4-2.7.
Section 3.1, p.448, specifies the classes factoring through an actual finite
Galois quotient. The adapter exposes that support condition for a supplied
group map without providing the global spanning theorem. The original retained
PDF pages 1 and 7-10 were read for this adapter.

Source ID: `henniart-2000-simple-proof`.
PDF SHA256:
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

This group-level adapter is a derived generalization. Its specialization to
the actual local Weil group of each p-adic field remains required. No local
field, Frobenius convention, reciprocity map, irreducible decomposition, or
global restriction is supplied by this module. Dual and character-twist
operations will use the parameter branch's actual operations once available.
The automorphic-side lattice still requires genuine supercuspidal classes and
must not be replaced with all irreducible GL_n classes. No character
orthogonality, isometry, spanning, or numerical finiteness theorem is assumed.

## Exact dependencies and validation

Both definition dependencies are accepted and published at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`:

- `Langlands/VirtualRepresentation/Integral`, artifact
  `b8c38a4e-6268-44a4-b9cd-99d752b42e47` version 1, integration
  `9036228c82344befae9d72050c3f0295`. Lean SHA256:
  `785418baa91b4ed140707b9a2a4acdd05b0f6ef9dab0efe3f271e2fef76a652d`.
- Worker 17's `Langlands/Weil/Representation/{Basic,Predicates}`, artifact
  `9bc9ac90-547a-485c-a632-039a3e1214a7` version 1, integration
  `6dea9fb977784cfa93d8d9b241e063f3`. Basic Lean SHA256:
  `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b`;
  Predicates Lean SHA256:
  `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148`.

The effective files, full final reviews and current availability were checked.
The dependency Lean and Markdown bytes match those used for development.
The prepared environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1
pins Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

This adapter and its private constructor/formula diagnostics compiled
successfully. Its independent semantic acceptance and publication are separate
requirements; no such acceptance is inferred from compilation.

Author of this adapter: Worker 24. Imported representation definitions remain
Worker 17's work and are used as exact published dependencies.
