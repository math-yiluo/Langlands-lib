# Local adapter from intrinsic root-datum compatibility

This internal derived module adapts an explicitly supplied proof of
`AffineSplitSurjectionRootDatumStatement` to actual compatible character maps
and then local torus conjugators. The intrinsic proposition remains an
explicit premise of each existence theorem.

`HasRootDatumTorusCharacterMap` is a proposition about an actual homomorphism
tau between coordinate split tori and two finite reduced root data P and Q.
It asserts the existence of p and `r : RootDatumIsogeny p Q P` such that tau
pulls every fixed-exponent target character back to the source character
with exponent r.weightMap. It imposes no ambient group or local-ring
hypothesis.

`splitTorus.exponentCharacter_comp_eq_of_points` converts an equality of
exponent monomials on all scheme tests into equality of the corresponding
actual character morphisms. The proof uses the monomial evaluation formula
and injectivity of the multiplicative-group point coordinates, followed by
extensionality of group-scheme homomorphisms.

`hasRootDatumTorusCharacterMap_of_affineSplitSurjectionRootDatum` works over
any commutative local ring R. It takes affine reductive groups G and H with
closed fibrewise maximal coordinate tori and supplied finite reduced
fibrewise root data. A finite surjective ambient homomorphism phi has tau
as its torus restriction. Published local root-weight-space freeness supplies
the rank-one trivializations required by the intrinsic proposition.

Apply its local clause at the closed point of Spec R. Every open neighbourhood
of this point is the whole spectrum, so its monomial formula holds on every
scheme test over Spec R. The character extensionality lemma then proves
`HasRootDatumTorusCharacterMap`. The characteristic-vanishing clause is
unneeded for this adapter.

`hasCommonRootDatumTorusMap_of_affineSplitSurjectionRootDatum` adds a second
ambient map Phi with the same torus square. Both maps therefore use the same
supplied tau, compatible root-datum isogeny, and character formula.
`RelativeIsogeny.fppfLocallyTorusConjugate_of_affineSplitSurjectionRootDatum`
also assumes Phi finite and invokes the local conjugator construction to
produce `FppfLocallyTorusConjugate`. Surjectivity is required only for phi
in this construction.

The provenance is the composition of the intrinsic proposition's stated
local conclusion, local root-weight-space freeness, the closed-point topology
of a local spectrum, actual exponent-character evaluation, and the preceding
supplied-root conjugator theorem. No claim is made to prove the intrinsic
proposition or the unconditional reductive-isogeny rigidity statement.
