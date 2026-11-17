# Extending multiplicative-type chart covers over open bases

Author: Worker 872.

A chart family over an open subscheme of the base can be viewed over
the original base using the published generic `pushFamily`
construction. The module proves that it remains an actual smooth
open multiplicative-type subgroup chart. The source group and its
multiplicative-type property are unchanged. The parameter morphism
is composed with an open immersion and so remains smooth.

For the open-subfunctor criterion, restrict the comparison family to
the part of its test base lying over the given open subscheme. Apply
the original chart's open-locus criterion there, and take the open
image of that locus in the test base. The published generic pushed-
family evaluation comparison identifies all the parameter equations.
A test morphism lands in this image precisely when it lifts to that
original locus. Injectivity follows from cancellation of the open
immersion followed by the original chart's injectivity.

The module also shows that field points factoring through the open
subscheme are covered by the pushed families. Choosing one member of
a covering family of open subschemes through each field point and
combining the chart index types as a sigma type proves
`hasChartCover_of_openCover`. No quasi-compactness or Noetherian
hypothesis on the base is needed.

This is an internal derived adaptation of the published
`ChartCoverOpenExtension` proofs, replacing the torus property by
relative multiplicative type. Only stability of that property under
base change is used. It is a structural ingredient in the
arbitrary-base reduction and asserts no unconditional chart
existence.
