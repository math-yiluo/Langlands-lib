# Smooth connected models at every depth

Let `F` be a nonarchimedean local field and `T` a torus over
`K = inertiaFixedField F`. At each nonnegative real depth,
`minimalCongruentConnectedModel` proves `MinimalCongruentConnectedModelStatement`
by taking `minimalCongruentModel` over `O = fixedFieldIntegers F`. The subtype
property gives smoothness, geometric connectedness of the fibres, and equality
of the integral-point subgroup with `minimalCongruentPoints`.

The construction starts from the connected Néron model when the fractional
part of the depth is zero and from the shallow dilatation when it is positive.
A positive integer part gives the corresponding congruence model of that
starting model.

This proves the model existence and fibre connectedness over `O` used in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition B.10.10,
printed p. 690, PDF p. 721. The source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
