# Source refinements aligning full cones with good pair charts

This internal construction supplies an actual downward-closed locally
refining source selection for a commuting compatible strong cone. It does
not assume an output atlas or a global cone lift. Field, space and index
universes are independent; no global Hausdorffness is assumed.

`HasOpenHausdorffContainer` selects original factor charts whose ranges lie
in an open Hausdorff subspace. It is downward closed and, under domain
saturation, locally refining: choose an open Hausdorff neighborhood at the
specified point and use an original subchart retaining a relative
neighborhood in the parent chart.

`alignedSourceCharts` selects original source charts whose two complete
cone images land in the factor charts of one good pair with an actual
original common base. It is downward closed.

For local refinement first pull back the two Hausdorff factor selections
along the cone legs, using the existing source-refinement theorem, and
intersect them. A selected source chart has its two images inside good
factor charts. Choose their original target base charts. The commuting
cone puts the composite image in their intersection. The base atlas net
supplies a finite relative neighborhood of contained original base charts.
Pull each of those domains back to the source chart and to both factor
charts using domain saturation. The two factor pullbacks form a good pair
with that common base, and the corresponding source pullback maps into
both factors. Continuity of the composite pulls the finite base
neighborhood back to a finite relative source neighborhood.

`alignedSourceSelection` bundles the resulting carrier, downward closure
and proved local refinement. Saturation is explicit for the original cone
source and two factors; only the ordinary atlas net is used on the base.
This is an alignment prerequisite for full cone lifting. It neither
constructs the complete lift nor proves the same-universe etale pullback
or etale projection. No external statement is transcribed.
