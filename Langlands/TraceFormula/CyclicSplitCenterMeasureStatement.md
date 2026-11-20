# The positive scalar measure in the discrete trace comparison

In `Langlands.TraceFormula`, `adelicPositiveScalar` maps a positive real
unit to a scalar matrix in the actual adelic group. The finite coordinates
of the idele are one and the same positive unit occurs at every infinite
place. A `UnitarySplitCenterCharacter` is a continuous homomorphism on this
positive real group with values of complex norm one. `normPullback` composes
it with the degree power map, which is the norm on these ideles.

The common one-dimensional Euclidean coordinate in II.1, printed p. 83,
is dual to the upper rational determinant norm character. Under geometric
restriction to the base this character becomes the `l`th power of the
base determinant, where `l = [E:F]`. For an upper scalar `exp(x)` the
coordinate is `n [E:ℚ] x`, and for a base scalar `exp(y)` it is
`n l [F:ℚ] y`. `cyclicUpperCenterMeasure` and `cyclicBaseCenterMeasure`
pull back Lebesgue measure by these respective coordinates, with the same
choice of unit Euclidean scale on the common line.

`CyclicSplitCenterMeasureStatement` takes positive rank `n` and an extension
of number fields in independent universes. It gives the norm on the actual
positive ideles and the pushforward of the upper measure by `x ↦ l x`.
Because `[E:ℚ] = l [F:ℚ]`, the two measures agree in the common scalar
parameter before applying the norm. After applying it the pushforward is
`1/l` times the base measure. This is the change of variables `da' = l da`
on printed p. 198. The actual idele norm formula is already in the Library
as `AdelicFunctoriality.ideleNorm_positiveRealIdeles`. The measure proof
uses the tower formula and scaling of Lebesgue measure.

`cyclicCentralAverage` is the central translate integral that implements
II.(17.8) on full adelic matrix tests, evaluated on the norm-one group when
passing from full tests to the norm-one distribution. The character occurs
with a positive sign in its argument, as in the definition on p. 198. Its
base and upper instances use the displayed measures and the base character
and its norm pullback. The distribution comparison is a further statement.

This is a coordinate formulation of Arthur and Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989), II.1 and
(1.6), printed pp. 83–85, II.(17.7)–(17.8), printed p. 198, and III, p. 203.
Registered source `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
