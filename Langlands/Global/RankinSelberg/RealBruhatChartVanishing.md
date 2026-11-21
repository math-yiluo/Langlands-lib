# Vanishing on lower real Bruhat charts

`Langlands.Global.RankinSelbergGlobal.RealBruhatChartVanishing.RealBruhatChartVanishingStatement`
concerns a distribution on the product chart of a real Bruhat cell indexed
by a permutation other than the reversal. The distribution is assumed to
vanish on tests supported off the cell, to have zero left infinitesimal
character on the upper matrix entry directions, and to have a nonzero
right infinitesimal character given by the sum of the adjacent entries.
The conclusion is that the distribution is zero on the chart.

An adjacent ascent gives the paired stabilizer field. The Lean proof
expands its left and right generators in the upper matrix entry directions
with smooth weights. The right weighted character is constant because the
sum of the adjacent entries of the right generator is one. Combining the
infinitesimal equations gives an eigenvalue equation with a scalar
correction from the differentiated weights. The correction vanishes along
the cell. Indeed, it is the trace of the varying field derivative minus
the trace with the weights held fixed. The varying derivative is nilpotent,
and the fixed-weight derivative is conjugate to the nilpotent ambient
paired generator by the chart derivative. Applying the zero-section
vanishing theorem finishes the proof.

This internal support-removal result uses the infinitesimal covariance
laws in chart coordinates.
