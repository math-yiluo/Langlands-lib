# Smooth norm-one character twists of actual unitary supports

This internal construction is a local support adapter for the relative isometry operation proof. It transports a supplied support witness and asserts no existence of supports or global automorphic lifts. The field and representation universes remain independent.

`unitarySmoothCharacterTwistBasisEquiv` specializes the genuine unitary supercuspidal basis twist to a smooth field character composed with the determinant in each positive rank. Openness of the character kernel pulls back along the continuous determinant. The norm-one hypothesis is precisely what preserves the actual invariant positive Hermitian form. `unitarySmoothCharacterTwistLatticeEquiv` extends this genuine basis equivalence over the integers and computes on every generator.

`unitarySmoothCharacterTwistDatum` transports that equivalence through the published actual unitary datum/basis equivalence. Its comparison theorem shows that forgetting unitarity gives exactly `CuspidalDatum.characterTwist`, retaining the same rank and actual twisted supercuspidal class. Multiset induction proves that encoding the transformed data agrees with the integral lattice twist, including all multiplicities.

Finally `isUnitaryLatticeSupport_smoothCharacterTwist` maps the actual unitary multiset from a supplied support witness. It applies `IsSupercuspidalSupport.characterTwist` to its underlying multiset and uses the encoding identity to obtain the required unitary lattice element. The resulting representation is the actual smooth twist by the determinant character.

All claims are derived from the published genuine class and unitary lattice twists, the actual unitary support encoding, and the proved arbitrary smooth-character support transport. No unproved classification statement or local Langlands result is used.
