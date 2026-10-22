# Duality on the genuine irreducible integral lattice

Author: Worker 24.

For a topological group `G`, this module constructs the involution of genuine
continuous irreducible complex representation classes across all positive
ranks, and extends it to their free integral lattice. The group and
representation-carrier universes are independent. The topological group
assumption is needed by the published continuity theorem for the dual.

`dualBasisEquiv` applies
`FiniteRepresentation.continuousIrreducibleDualEquiv n` in each rank.
The rank is unchanged. `underlyingClass_dualBasisEquiv` proves that forgetting
rank, continuity and irreducibility gives the genuine dual isomorphism class.
The representative formula `dualBasisEquiv_basisClass` identifies this operation
with the full algebraic dual of an actual representation, with its proved
continuity, irreducibility and rank certificates. The basis equivalence is
its own inverse, and its square is the identity.

`dualLatticeEquiv` uses the existing `reindex` construction to extend that
basis involution by integer linearity. The single-coefficient and generator
formulas describe its action explicitly. The coefficient of a dual class is
the original coefficient. The linear equivalence is its own inverse and
its square is the identity. It preserves the rank-weighted integer degree,
the integral coefficient pairing, and membership in the effective cone.

The implemented basis proofs use the published rank-wise dual equivalence,
its inverse law and forgetful formula. The lattice inverse and composition
proofs use Mathlib's `Finsupp.domLCongr`. Degree and pairing preservation use
finite-support linear induction and the generator/coefficient formulas.
Preservation and reflection of effectiveness use the surjectivity of the
basis equivalence. Thus the pairing assertion concerns the specified
coefficient pairing; it invokes no character orthogonality, local factor
comparison, or correspondence.

## Provenance and boundaries

This is a derived construction from the published
`Langlands.VirtualRepresentation.Weil.Generic` and
`Langlands.Weil.Representation.DualClasses`. The former supplies the genuine
positive-rank basis and finite-support integral lattice; the latter supplies
the actual dual involution on each rank using finite-dimensional evaluation
onto the double dual and the published continuity/irreducibility theorems.
All new code in this pair is by Worker 24. The imported dual construction and
its source correspondence are documented in the `DualClasses` pair.

The mathematical motivation is the representation-class lattices and dual
operations in Henniart (2000), sections 1.1--1.2 and 2.4--2.7, printed
pp.439--440 and 445--447, literature ID `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
These passages were read in the retained original. The sigma-type and
finite-support implementation and its intrinsic identities are derived,
rather than translations of further literature assertions.

This module does not assert preservation of unitarity, finite image, Galois
type, or factorization support. Unitary restrictions require the separate
unitary-operation proofs. Specialization to the actual local Weil group is
also separate. The ambient free lattice is not identified with an exact
Grothendieck group.

The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
