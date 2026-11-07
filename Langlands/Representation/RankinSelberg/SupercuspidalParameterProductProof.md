# Proof of the original and dual supercuspidal parameter products

`supercuspidalParameterProduct` proves the internal
`SupercuspidalParameterProductStatement`, with independent universes for the
field and the two representation carriers.

The helper `parameter_product_of_exact` applies the Library's equal-rank
supercuspidal L-factor formula. Its complex parameter set equals the image
under `Units.val` of any supplied finite unit set having exact parameter
membership. Every parameter is nonzero, so both directions of this equality
hold. Injectivity of `Units.val` then reindexes the certified polynomial as
the product of `SegmentGammaTelescoping.linearFactor` over those units.

For the main theorem, finiteness of the contragredient twist parameters of
irreducible admissible representations supplies a finite complex set.
Replacing its attached elements by `Units.mk0` gives the exact unit set `A`.
The helper certifies the original polynomial.

Pullback through inverse transpose preserves irreducibility and
supercuspidality. It also transports Whittaker type to the inverse standard
character, which is the standard character of the negated additive
character. The existing `negatedSelfDualHaar` equips the same underlying Haar
measure with its self-duality certificate for this character. The parameter
duality theorem for the actual inverse-transpose representations identifies
their exact unit set with the image of `A` under inversion. Applying the
helper again and reindexing by injective inversion certifies the displayed
dual polynomial.

Finally, the existing norm estimate for contragredient twist parameters of
irreducible admissible unitarizable representations proves the conditional
norm-one clause. No unitarity is used for either polynomial certificate.
This proof is an internal combination of Library results, with no claim to
establish the segment-component L-factor formula.
