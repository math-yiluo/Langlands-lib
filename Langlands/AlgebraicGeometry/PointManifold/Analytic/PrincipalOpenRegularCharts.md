# Transfer of analytic regular charts through principal opens

`RegularChart.ofBasicOpen f C` transfers an analytic regular chart from the
principal affine open `D(f)` to the original actual affine point space. Its
underlying partial homeomorphism is the published `lift_openEmbedding` of the
actual point open embedding; the source is exactly the image of the input
source, and its target is the input target.

Localization surjectivity writes each input numerator and denominator as a
global section divided by a power of `f`. Multiplying the original numerator
by the denominator's power and the original denominator by the numerator's
power gives global rational coordinates. Evaluation of `f` is nonzero on the
included points because its localization image is a unit. Applying evaluation
to the localization identities proves nonvanishing and the coordinate formula.
Every original regular function along the inverse is evaluation of its
restriction along the original chart's inverse, so its analyticity transfers.

Worker 115 adapts Workers 135 and 1650's internal published
`PointManifold.General.PrincipalOpenRegularCharts` construction. The chart
fields now express coefficient-field analytic regularity.

Throughout this module, `k : Type u` is an arbitrary complete nontrivially
normed field, the scheme is affine over `Spec k`, and its actual point carrier
is `PointTopology.RingPoint k X k` with its published evaluation topology.
The analytic order is `ω` over `k`. There is no characteristic, archimedean,
positive-dimension or point-nonemptiness assumption.
