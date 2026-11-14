# Canonical residue transporters from equality at a field-valued point

This internal comparison module constructs an actual canonical residue point and
the identity transporter between two cocharacters whose normalized pullbacks
agree at a supplied field-valued point. It assumes no affineness or smoothness
of the base or target.

`baseChangeCocharacter_injective` uses faithful pullback on the category of schemes
over the base to reflect equality of group-scheme homomorphisms, after cancelling
the multiplicative-group base-change isomorphism.
`cocharacter_eq_residue_of_fieldPoint` factors the supplied field-valued point
through the canonical residue field of its image. The intervening field extension
is faithfully flat and quasi-compact. The pullback tower comparison converts
equality over the supplied field to equality after this faithful pullback, which
then reflects to the residue field.

`ResidueCocharacterTransporterData` records a base point and an actual all-test
transporter between the two raw residue pullbacks.
`residueCocharacterTransporter` uses the image of the supplied field point and
the identity group point. Cancelling the multiplicative-group comparison
converts the reflected normalized equality to equality of raw pullbacks, so the
identity satisfies the transporter equation on every test scheme.

The construction is derived from the Library's field-point factorization,
field-extension fpqc theorem, transporter relation, and pullback comparisons,
together with Mathlib's faithful fpqc pullback instance. It introduces no new
source-derived mathematical assertion.
