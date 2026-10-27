# The actual horizontal finite adelic action

Let `F` be a number field in arbitrary universe `u`, let `n` be any natural
rank, and let `S : OperatorRealization F n` be an actual operator realization.
The coefficients are complex and the carrier is the existing `S.Space` inside
the stable automorphic function space. The constructions use the existing
horizontal full-compact-equivariant alternating cochains on the actual reduced
complex Lie algebra. Every natural degree, including zero, is allowed.

`finiteCompactIntertwiner d` retains the actual finite translation
`S.finiteRepresentation d` as its linear map. Its compact intertwining equation
is the proved commutation of finite translation with the full compact action.
`finiteReducedLieHom d` retains the same linear map as a map of the actual
reduced Lie module, using the proved commutation with the reduced Lie action.
Neither construction requires an additional compatibility hypothesis.

`horizontalFiniteRepresentation q` is a representation of the actual
`FiniteAdelicGL F n` on
`horizontalEquivariantSubmodule F n S.compactRepresentation q`.
It postcomposes coefficient values by `finiteCompactIntertwiner d`, using
`horizontalMapCoefficients`. Thus it preserves every-slot horizontality and
equivariance under every element of the standard infinite compact group.
The application formula is

`(S.horizontalFiniteRepresentation q d f).val X =
  S.finiteRepresentation d (f.val X)`.

The identity and multiplication laws follow from the corresponding laws of
`S.finiteRepresentation`, after subtype and alternating-map extensionality.
In particular, multiplication applies the second translation first, in the
same convention as the existing finite representation.

This is an internal postcomposition construction. Its provenance is the
actual finite and compact actions and their commutation in
`OperatorCompactCompatibility`, the reduced Lie action and finite commutation
in `HorizontalDifferential`, and the existing horizontal coefficient-map
construction in `ArchimedeanHorizontal` and `HorizontalAlternating`.
No external identification is asserted. This module constructs the algebraic
finite representation; it does not assert continuity or smoothness of the
entire horizontal representation, differential commutation, square zero,
or cohomology.

Authorship: Worker 2.
