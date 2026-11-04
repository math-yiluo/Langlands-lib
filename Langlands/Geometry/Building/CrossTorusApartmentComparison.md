# Comparing transported and separately supplied valuation apartments

Author: Worker 118.

Over an arbitrary field, take actual isomorphisms `e : S ≅ S'` and
`f : G ≅ H` with the original commuting square of inclusions `i`, `j`.
Assume monomorphisms on the underlying inclusions and affine structural
morphisms on both ambient groups. Supply source data `D : KPApartmentData i ω`
and separately specified target data `E : KPApartmentData j ω`, with the same
function `ω : kˣ → ℝ`.

A single source point `x₀` whose transported full valuation family lies in
`E.carrier` identifies the entire transported data with `E`. Indeed, two
full equipollence classes for the same inclusion that contain a common family
have the same carrier, by the existing membership/equipollence characterization.
Carrier extensionality then identifies the data. Conversely, if the transported
data equal `E`, any source point provides such a witness. This proves the exact
criterion `transport_eq_iff_exists_mem`; it does not construct a witness for
arbitrary independently specified classes.

`D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀` constructs the actual
affine equivalence to `E.Apartment` from this one witness. It composes the
existing actual apartment equivalence with the identity on valuation families
between equal carriers. Quotient induction proves that the latter identity
is affine, with identity derivative. The resulting derivative is precisely
`translationSpaceTransportEquiv e f h`, and the underlying point value is
the original full-family transport. The comparison intertwines the original
source and chosen target normalizer actions and preserves every valuation
value on simultaneous actual character and point images.

Different choices of the witness give the same affine equivalence, since their
points have identical full valuation families. More generally, any affine map
with those prescribed underlying families equals the constructed comparison.
This is independence of the class-identification witness for fixed source and
target data and fixed actual isomorphisms.

`D.apartmentConjugationAffineEquivOfMem` specializes this construction to
the actual inner automorphism associated with a rational point `g`, a supplied
isomorphism of acting groups, and their conjugation square. It still requires
one transported source valuation in the specified target class. The intrinsic
value identity uses exactly `g*u*g⁻¹` in the target and the same value as at
`u` in the source. Its derivative is the existing quotient map induced by the
actual torus isomorphism.

The provenance is internal: full-orbit membership, carrier extensionality,
the actual family/apartment maps and the published inner-automorphism point
formula give all constructions and identities. No global compatible family
of apartment data is constructed. In particular the existence of the matching
point for canonical conjugate apartments, common-building realization,
apartment intersections, full A2 and general building existence remain
separate obligations.
