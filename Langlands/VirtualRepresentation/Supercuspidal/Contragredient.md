# Unconditional smooth contragredients on the supercuspidal lattices

This module supplies the actual smooth contragredient on the integral lattices
of positive-rank supercuspidal classes over a p-adic field. The field realization
has universe `uF`, representation carriers have an independent universe `uV`,
representation coefficients are complex, and lattice coefficients are integers.
The group in each rank is the actual `GL_n(F)` with the field's canonical
topological data. Representation carriers need no topology, norm, completeness
or finite-dimensionality assumption.

## Provenance and dependencies

This is an internal specialization of the published constructions in
`Langlands.VirtualRepresentation.Supercuspidal.Dual` and
`Langlands.VirtualRepresentation.Supercuspidal.UnitaryDual`. It supplies their
proof arguments with the published theorems
`GeneralLinear.supercuspidalContragredient` and
`Classification.unitaryAdmissibleHermitianClause F F.canonicalTopologicalData`.
The former proves `GeneralLinear.SupercuspidalContragredientStatement.{uF,uV}`;
the latter proves the admissible Hermitian identification for every invariant
positive form. Neither theorem adds a hypothesis to the operations here.
The four equivalences are reducible abbreviations of the existing constructions;
every law is a direct specialization of its corresponding published law.

The smooth contragredient means the smooth-functional subspace of the
inverse-transpose algebraic dual. The imported dual construction descends this
operation to isomorphism classes and proves its involution by actual admissible
biduality. On unitary classes, the Hermitian identification and conjugate-linear
form transport give preservation of the existence of an invariant positive
Hermitian form; the class involution gives reflection. The present module
reuses these proofs and the original source conventions documented in its
imports.

## Ambient operations

In `Langlands.VirtualRepresentation.PadicSupercuspidal`,
`contragredientBasisEquiv F` is an involution of the genuine supercuspidal basis
across all positive ranks. The `_mk` theorem identifies its action in a fixed
rank with the actual class smooth contragredient. It retains rank, is its own
inverse, and composing it with itself gives the identity equivalence.

`contragredientLatticeEquiv F` extends this basis permutation integrally.
It sends each integer singleton and each generator to the singleton or generator
of its dual class, retaining its coefficient. The coefficient at a dual class
is the original coefficient. It is its own inverse and its square is the
identity, both pointwise and as a linear equivalence. The degree is the
rank-weighted integral degree; it is preserved. Simultaneous duality preserves
the integral coefficient pairing and preserves and reflects nonnegative
coefficients.

The real-power twist laws negate the exponent of the existing normalized
determinant twist. The unramified twist laws invert every parameter `z : ℂˣ`,
with no norm restriction on the ambient basis or lattice. They retain the
published convention `z ^ ord`, where the order of a uniformizer is positive
one.

## Unitary operations

`isUnitaryClass_contragredientBasisEquiv_iff` proves preservation and reflection
of the genuine unitary subset. `unitaryContragredientBasisEquiv F` restricts the
ambient operation to this subset. Its value in the ambient basis is the ambient
contragredient. The representative theorem sends an actual unitarizable
supercuspidal object to its actual smooth dual, with the positive-form witness
supplied by the proved Hermitian clause. Rank, inverse, involution and
composition laws hold for this restriction.

`unitaryContragredientLatticeEquiv F` is the integral extension on the unitary
basis. Singleton, generator, coefficient, inverse and involution laws hold.
`includeUnitary_contragredient` shows that inclusion in the ambient lattice
commutes with duality. It preserves the unitary degree and integral coefficient
pairing, and preserves and reflects effectiveness. For a complex unramified
parameter of norm one, the restricted basis and lattice laws invert the parameter;
its inverse again has norm one.

All preservation and compatibility fields above are proved by the imported
construction laws with their theorem inputs discharged. The module does not
construct global generators, prove Brauer spanning or character faithfulness,
identify a free irreducible lattice with an exact Grothendieck group, or prove
an isometry between the Weil and automorphic sides of a correspondence.
