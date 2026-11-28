# Extending multiplication on the original square

`mulG` extends the original law followed by the original chart to a map
`Y ×_S Y ⟶ Gl`. At a point of the square, the slice of the universal
left translation imposes that `c⁻¹x` be defined for the chosen section
`c`. The other slice imposes that `(c⁻¹x,y)` belong to the domain of the
law. The relevant opens are fibrewise dense over the square, which lets
`HasSectionLifts` choose `c`.

In the neighbourhood presented by `(w,y) ↦ (cw,y)`, the extension sends
the pair to the chart of `c` at `wy`. On a dense open where the original
and chart products are defined the formula agrees by associativity and
`dom_chart`. The extension lemma glues these pieces.

This obtains the extension on `Y ×_S Y` of BLR, *Néron Models*, §5.3
Lemma 6, pp. 125–126, using the already glued section charts.
