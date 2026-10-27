# Actual equivalences from ordered product regrouping

Author: Worker 645.

This internal adapter requires a proof of the published proposition
`Langlands.Parabolic.OrderedProductRegrouping.{uF,uV} F T` as an explicit
argument. It does not supply that proof.

For exactly the original shape `B`, outer shape `D`, refinement `S`, nested
label equivalence `e`, size equalities `h`, and consecutive-coordinate identity
`hc` of that proposition, `normalizedProductRegroupingEquiv` chooses the
asserted categorical isomorphism and applies the published
`SmoothRep.equivOfIso`. Its source and target are the actual representations
underlying the flat and nested normalized product objects. The inner factors
are the literal equality-transported smooth objects
`(h ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩)`; no rank identifications are omitted.

`normalizedProductRegroupingToEquiv` additionally takes a family `τ` of desired
outer factors and actual representation equivalences `δ j` from each inner
normalized product to `τ j`. It composes the preceding equivalence with
`normalizedProductInducedEquiv D δ`. Thus the source is the flat normalized
product on `σ`, and the target is the normalized product on exactly `τ`.
The second map applies the external tensor of the supplied factor maps to
function values, as in the published block-equivalence construction. No
specific evaluation formula is claimed for the chosen first map.

The field and original carrier universes `uF,uV` are independent, and `τ` has
an independently selected common carrier universe `uW`. Inner carriers and
the source carrier lie in `max uF uV`; the final target carrier lies in
`max uF uW`. Smoothness of `σ` is included in its bundled objects. No
smoothness condition on `τ` is needed for the second, already smooth induced
space. Total rank zero remains allowed.

The provenance is direct internal composition of the published category
conversion and block equivalence APIs. These definitions retain regrouping
as an assumption and do not establish any unconditional regrouping or
three-block associativity statement. The latter consumer must supply the
published proof of regrouping and independently verify its literal geometry,
inner-factor comparisons, and ambient rank transport.
