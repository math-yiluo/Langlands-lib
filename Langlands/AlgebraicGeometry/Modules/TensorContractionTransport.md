# Tensor contraction on original opens

For a genuine trivialization `t` of `N` on an open `U` of a scheme `S`,
`lineBasisSection t V h` is the section of `N` over any smaller original open
`V` whose `lineCoordinates` value is one. The coordinate equivalence supplies
this section and proves its displayed coordinate value.

`ofImage_pureSection` identifies the actual restriction comparison on pure
sections. `lineCoordinates_eq_chartE` identifies the genuine linear coordinate
equivalence with the existing section chart `chartE`.

`modE_tensorRestrictionTrivialization_pureSection` proves that contraction
on an original open sends a pure tensor of `m` and `n` to
`lineCoordinates t V h n` times `m`. The proof unfolds `modE`, restricts the
pure section, applies the restriction comparison and the already proved local
contraction formula, then transports the scalar using the structure-sheaf
isomorphism. Linearity and inverse restriction maps give the result.

`modE_tensorRestrictionTrivialization_symm` proves that inverse contraction
sends `m` to the pure section of `m` and `lineBasisSection t V h`. Its proof
uses injectivity of contraction, the inverse-isomorphism transport law and the
pure-section formula above.

These are derived consequences of the existing tensor restriction and section
transport APIs. Cross-open dual-frame comparison, projective gluing and ordinary
moduli representability remain further obligations.
