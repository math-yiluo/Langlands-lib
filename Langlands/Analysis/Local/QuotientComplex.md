# Complexification of compact quotient averaging

This internal construction extends a map on real compactly supported continuous
functions to complex functions by applying it separately to the real and imaginary
parts. The definition is

`complexifyCompactMap P f = P (Re f) + i P (Im f)`.

The result is again continuous with compact support. Linearity, positivity,
surjectivity, and the existence of a quotient measure are not assumptions of this
construction. If integration of `P f` against a supplied measure agrees with
integration of `f` against the ambient measure for every real test function, the
same formula holds for this complexification. Both measures are assumed finite
on compact sets, and their measurable structures are Borel.

For the existing left quotient `LeftQuotient H`, the helper assumes that `P`
evaluated at the class of `g` is exactly
`∫ h : H, f (h.val * g) ∂μH`. For each complex test function under consideration,
it also assumes integrability of every complex fiber function. The helper then
identifies its compact complexification with the published `quotientAverage`.
Consequently the latter is integrable against any quotient measure finite on
compact sets, and the real integral formula implies the published complex
integral formula.

The proof uses the bundled real and imaginary parts of a compact test function,
Mathlib's compact support operations, and the Bochner integral identities
`integral_re`, `integral_im`, and `integral_re_add_im`. Equality on the quotient
is proved by induction on representatives. This is a derived API construction
from those identities and the published quotient conventions, with no external
literature claim.

This unit does not construct the real averaging map, prove fiber integrability,
construct a quotient measure, or establish nonzeroness, regularity, or invariance.
Those remain independent inputs to the full compatible-measure existence proof.
