# Choosing section charts in families

`chart_shift` rewrites the chart of `b` at `y` as the chart of `d` at
`(d⁻¹b)y`, when the indicated partial products are defined. The equality
follows from `sectionPair_mulG` and `mulG_assoc_pt`.

For a chart index `j` and a morphism `y : P ⟶ Y` over `S`, `chartCover`
constructs an open immersion into `Y ×_S P` with fibrewise dense image.
For the original chart, this open tests whether `y` lies in the image
of left translation by a section. For the chart of `b`, the slice of
the universal translation and the domain test for `(d⁻¹b)y` give the open.
A section lifting into it on a neighbourhood places the given chart
coordinates in its section chart. This derives the chart choices for the
subsequent multiplication and division constructions from the section
translation relation in BLR, *Néron Models*, §5.3, pp. 122–123.
