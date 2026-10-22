# Genuine operations on the unitary irreducible lattice

Author: Worker 24.

This derived construction restricts the published genuine character-twist and
contragredient equivalences to the actual unitary classes of continuous
irreducible complex representations across positive ranks. Group and carrier
universes remain independent. Twisting requires a continuous character whose
values all have complex norm one. Duality additionally requires a topological
group, as in the existing continuous dual-class equivalence.

The unitary predicate is the published existence of an actual representative
carrying an invariant positive Hermitian form. The forward preservation proofs
twist or dualize that witness, use the proved preservation theorem from
`Langlands.Weil.Representation.UnitaryProof`, and identify its actual isomorphism
class by the forgetful formulas in `Weil.Twist` and `Weil.Dual`. Reflection uses
the inverse modulus-one twist or the dual involution. No form, representative,
or preservation certificate is added as input to the lattice construction.

`unitaryTwistBasisEquiv` and `unitaryDualBasisEquiv` restrict the existing basis
equivalences using these proved equivalences of predicates. Their values in the
ambient basis are the genuine operations and preserve the positive rank.
The inverse twist is the inverse character; the dual equivalence is its own
inverse. Their integral extensions reindex finite integer coefficients.
The single-generator and coefficient formulas explicitly record this action.

The inclusion into the full irreducible lattice intertwines both operations.
These equalities are proved by finite-support linear induction, reducing to
single coefficients. They imply preservation of the unitary degree from the
ambient degree-preservation theorems. The unitary coefficient pairing is
preserved by linear induction and the coefficient formulas. Surjectivity of the
basis permutations proves preservation and reflection of nonnegative
effectiveness. Pairing preservation uses no character orthogonality.

## Provenance and scope

The construction is internal derivation from the published `Weil.Generic`,
`Weil.Twist`, `Weil.Dual` and `Weil.Representation.UnitaryProof` interfaces,
using Mathlib's equivalence restriction and finite-support reindexing. The
preservation proof is imported as a theorem; no statement is assumed.
Henniart (2000), section 1.1 footnote 1 and section 1.2(2)-(3), printed
pp.439-440, gives the unitary, twist and contragredient conventions. Sections
2.5-2.6, printed pp.446-447, motivate their integral extension and the pairing
on the specified unitary basis. These passages were read in the original
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

This module makes no cross-side isometry claim. Finite/Galois-type support,
unramified-orbit finiteness, global images and irreducible decomposition remain
separate obligations. Arbitrary nonunitary twists act only on the full lattice
through the existing construction.
