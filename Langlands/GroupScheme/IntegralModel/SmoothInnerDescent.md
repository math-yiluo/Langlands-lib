# Smooth inner descent of a supplied stable integral model

This internal module combines exact common finite recovery with the smooth
finite inner construction, actual given-integer recovery and compatibility
with every inertia-field automorphism. It claims no original-literature
theorem. All fields and schemes have a common arbitrary universe.

`HasSmoothInnerDescent` is a Prop-valued predicate on the original group
G, supplied inertia-integer model P and prescribed cocycle values c. It
requires a group H over F, a smooth model M over the given valuation
integers of F, and an actual isomorphism f from H's inertia-field extension
to G's. The predicate retains a compatible isomorphism from the actual
unramified base change of M to P over precisely f. It also records equality
of their original integral-point images after transport by f, and
`InnerGaloisCompatible` for every inertia-field automorphism. H remains the
descended group's own generic fibre and is not identified with G over F.

`innerDescent_of_finiteInnerRecoveryAt` assumes an actual finite Galois
arithmetically unramified field inside the inertia fixed field, exact common
finite recovery of P and c, smoothness of P, and both forward and inverse
stability of its integral-point subgroup under the prescribed inner action.
The proof extracts the finite model, its exact recovery isomorphism, a
finite cocycle and recovery of every upstairs cocycle value. The lemma
`recovery_at_liftAutomorphism` supplies recovery at the chosen lifts used
in the finite inner construction. The witnesses are then exactly
`finiteInnerGenericGroup`, `givenFiniteInnerModel` and
`finiteInnerInertiaGenericComparison`. The previously proved smoothness,
compatible model isomorphism, point-image equality and all-automorphism
compatibility establish the predicate.

`exists_smoothInnerDescent` assumes G affine, P supplied and smooth, the
cocycle law for c, its triviality on the fixing subgroup of some finite
subfield of the inertia fixed field, and the same forward and inverse
integral stability. It obtains a single finite field with exact model and
all-value cocycle recovery using `exists_common_finiteInnerRecovery`, then
applies the preceding lemma. No finite recovery or effectivity premise
remains in this final result.

The supplied smooth model and its two stability premises remain explicit.
This module constructs no building stabilizer model, reductive residue
quotient, Frobenius comparison or chamber data, so it does not prove the
quotient theorem it serves.
