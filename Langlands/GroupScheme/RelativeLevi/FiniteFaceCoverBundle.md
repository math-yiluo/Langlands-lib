# The actual vector-bundle module of the assembled face layers

This internal unit for the relative radical filtration constructs the actual finite locally free module for the original
assembled face-weight layer group over the finite disjoint affine cover source.
Each component retains its original exact-support rank. The module is glued
from those actual free sheaves, and the group component comparisons and module
component comparisons construct its natural all-test point charts.

`layerRank` is the cardinality of the original exact face-weight support on each
component. `layerBundle` is the actual module obtained by disjoint free-sheaf
gluing, `layerBundlePieceIso` recovers its original free component, and
`layerBundle_isFiniteLocallyFree` provides actual covering finite local frames.
There is no common-rank premise or replacement by padded coordinates.

`layerComponentFreePoints` uses the original `layerComponentIso` and the actual
free-vector-group coordinates. The general `groupIsoPoints_natural` proves
naturality before specializing to these dependent root constructions.
`moduleIsoPoints` transports their sections through the actual pulled-back
module comparisons; its naturality follows from canonical relative section
pullback being natural in module morphisms.
Thus `layerComponentCharts` is constructed rather than assumed.

`layerBundlePoints` assembles those charts on every scheme test over the
coproduct base. `layerBundlePoints_natural` is the exact naturality equation for
canonical section pullback of this one actual module.
`isVectorBundleAdditive_layerGroup` combines this identification with proved
affineness and smoothness of the original assembled layer group to obtain the
unchanged vector-bundle additive predicate. Empty covers and rank-zero layers
are included.

Provenance: an internal derivation from the original face-layer group assembly,
actual disjoint free-module gluing, natural free-vector coordinates, and
all-test point/section assembly. Descent of this vector bundle from the affine
cover source to the original base, including the actual linear transition
cocycle for the original global quotient, remains a separate obligation.
