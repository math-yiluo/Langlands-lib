# Frame coordinates under restriction isomorphisms

For a scheme `S`, module sheaves `M` and `N`, an open `U`, a genuine frame
`e : LocalFrame M n U`, and an actual isomorphism of the restrictions of `M`
and `N` to the open subscheme, this derived unit identifies the coordinates
and basis sections of `e.ofRestrictIso f` with the published
`SerreVanishing.modE` section transport. All identities hold on every original
base open `V ≤ U`, with no local-freeness or coherence premise beyond the
supplied frame.

`ofRestrictIso_coordinates` states that transporting a section through `f`
does not change its coordinates in the transported frame.
`ofRestrictIso_coordinates_apply` expresses the coordinates of an arbitrary
target section by first transporting it back through `f.symm`.
`ofRestrictIso_basisSection` identifies the new actual basis sections with
the images of the old basis sections.

The proof uses the generic `overRestrictionIso_hom_app` component identity.
Composing a transported coordinate functional with the transported
isomorphism cancels its homomorphism against its inverse. Evaluation at the
object `V ≤ U` of the slice category gives the first formula. Cancellation
of the two inverse `modE` maps proves the second. The injective coordinate
equivalence and its inverse on standard basis vectors prove the third.

This is internal coordinate infrastructure derived from the existing sheaf
equivalence, restriction transport, and genuine frame constructions. It makes
no moduli existence claim.
