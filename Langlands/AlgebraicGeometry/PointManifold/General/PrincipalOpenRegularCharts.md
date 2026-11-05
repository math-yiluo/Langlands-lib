# Universe-general transport of regular charts through principal affine opens

This module adapts the published `PointManifold.PrincipalOpenRegularCharts` implementation by Worker 135
to `PointManifold.General`, with an explicit arbitrary coefficient universe
`u` and `k : Type u`. Worker 1650 made this universe extension. It uses the
published actual `RingPoint` carrier and evaluation topology, and leaves the
existing target and all its imported definitions unchanged. The construction
places no positive-dimension or point-nonemptiness premise on its input.

This internal derived construction transfers a `RegularChart` on a principal
open affine subscheme `D(f)` to the original actual affine point space. It uses
the published open embedding on actual points and clears localization powers
in the chart coordinates. Smooth inverse evaluation of original global sections
follows by evaluating their restrictions on the original chart.

`RegularChart.ofBasicOpen f C` uses the published topology on the original
`RingPoint` carrier. Its source is exactly the image of `C.homeomorph.source`
under actual postcomposition with the principal-open immersion, as recorded by
`RegularChart.ofBasicOpen_source`. It has the same target as the input chart.
This construction requires no chart-existence premise beyond the chart `C`
on `D(f)`. It works for every `RCLike k` and every natural dimension, including
zero.

The proof first gives the actual coordinate algebra of `D(f)` its localization
structure over the original coordinate ring. For each numerator `sᵢ` and
denominator `tᵢ` of `C`, localization surjectivity supplies global sections
`aᵢ`, `bᵢ` and natural powers `nᵢ`, `mᵢ` satisfying
`sᵢ fⁿⁱ = aᵢ` and `tᵢ fᵐⁱ = bᵢ` in the localized algebra. The transferred
coordinate has global numerator `aᵢ fᵐⁱ` and denominator `bᵢ fⁿⁱ`.
`regularEvaluation_openPointMap_algebraMap` identifies evaluation of restricted
global sections with evaluation after point inclusion, and
`regularEvaluation_basicOpen_ne_zero` proves that `f` is nonzero on the included
points because its localization image is a unit. Applying evaluation to the
two localization identities proves both nonvanishing of the new denominators
and equality of the rational chart coordinates.

The underlying partial homeomorphism is Mathlib's `lift_openEmbedding`,
applied to the published `isOpenEmbedding_basicOpenPointMap`. Its inverse
is the input inverse followed by actual point inclusion. Evaluating an original
global section after this inverse equals evaluating its pullback along the
input inverse, so the required real smoothness is exactly the input chart's
inverse-evaluation property.

This is an internal derived compatibility construction using the published
actual-point topology and regular charts, together with Mathlib's localization
and open-partial-homeomorphism APIs. It is not a transcription of a result
from external literature.
