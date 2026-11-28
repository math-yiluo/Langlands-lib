# The glued group scheme and its dense chart

On each chart of `Gl`, the domain of its translation is fibrewise dense.
The chart agrees there with the original chart at the translated point.
Transporting generizations over the base gives `original_chart_dense`.

Every point is in the chart of some section `c` by the common-chart
construction applied to a pair with that point as both projections.
Since this chart factors as `μ(c,−)`, the extension `mulG` is surjective.
Thus the glued scheme is quasi-compact as the continuous image of
`Y ×_S Y`. This yields finite type over the base when combined with
smoothness. `gluedGroup` represents the relative group law by a group
object over `S`, and `gluedGroup_mul` compares its multiplication with
`mulPts`. These are the properties of the group scheme and its open
immersion in BLR, *Néron Models*, §5.2 Theorem 3, p. 117.
