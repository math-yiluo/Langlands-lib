# The connected Néron model of a torus over the maximal unramified field

`Langlands.Geometry.Building.connectedNeronModel` gives an actual smooth
affine integral model of a torus over `K = inertiaFixedField F` for a
nonarchimedean local field `F`. Its base ring is `O = fixedFieldIntegers F`.
The model has geometrically connected fibres and its integral points inside
the given torus point group are exactly the norm-defined Iwahori subgroup
`T(K)^0`. The zero term of `localTorusFiltration` is this Iwahori subgroup
by `localTorusFiltration_zero`.

The construction chooses a finite Galois splitting field by
`localTorusSplittingData` and applies `unramifiedTorusIwahoriModel` with
that field. That theorem takes the relative identity component of the
smooth model of the maximal bounded subgroup. The chosen model comes with
smoothness, geometric connectedness and the integral-point equality.
The definition requires only the torus and the local-field hypotheses.

This is the connected Néron model `T^0` used in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition B.8.4(3) and
Corollary B.8.7, printed pp. 681–683 / PDF pp. 712–714. The latter identifies
its points with the Iwahori subgroup of Definition 2.5.13. The registered
source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
