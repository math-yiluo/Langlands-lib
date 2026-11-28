# Relative coroot evaluations for Weyl parameters

`realParameterPairing_splitDual` identifies the parabolic pairing
against a projected vector with the pairing of the restricted
parameter against the original vector on the maximal split torus.
It checks the identity on tensors and then uses additivity.

`relativeCorootDuality` uses the perfect split-torus pairing to
represent the fundamental weight of a simple root outside the Levi.
That weight vanishes on the coroots of the Levi because it is dual
to the full set of simple coroots. The representing torus character
therefore belongs to the coroot annihilator. The standard Levi
character theorem lifts it to a real parameter of the Levi. Pulling
that parameter back along the Levi retraction gives the required
parabolic parameter. Its pairing with the projected coroots is the
Kronecker delta. In particular, each complex coroot evaluation is
nonzero as a linear form, as seen by complexifying the dual parameter.

Composing a nonzero coroot evaluation with a surjective complex
linear map and a complex chart gives a nonzero form on the chart.
If the affine offset is nonzero, the origin witnesses nonvanishing.
If the offset is zero, vanishing at every imaginary point would
imply vanishing on the real slice and then on the whole chart by
complex linearity. This proves the imaginary witness condition for
each parameter map arising from an isomorphism of the Levis.

The Weyl map also preserves imaginary parameters because it is the
scalar extension of an integral character restriction. The real
part of its complex coroot value on the imaginary slice is zero.
Via a chart matching the real and imaginary parameters, this says
that the linear form has real values on real coordinates. These two
facts supply the nonvanishing and reality conditions of the
local affine divisor argument when the labels use these Weyl maps.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 5–6 and 24–25.
The relative coroots, their lattice and the denominator products are
used in (7.8), (7.9), and (7.12).
