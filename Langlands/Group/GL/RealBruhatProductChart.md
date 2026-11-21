# Smooth product coordinates for real Bruhat cells

`Langlands.GeneralLinear.RealBruhatProductChart.RealBruhatProductChartStatement`
gives an open smooth coordinate chart around each real upper Bruhat cell.
For a permutation `w`, the normal coordinate positions are the strictly lower
entries that remain strictly lower under `w⁻¹` on both indices. The tangent
positions are their complement. Every diagonal position is tangent, so the
source is the open nonzero diagonal condition on the tangent array times the
whole space of normal arrays.

The proof combines the two arrays by a continuous linear equivalence. The
trailing-minor chart turns the combined array into a matrix, and right
multiplication by the permutation gives the cell chart. Both directions are
smooth and the target contains only invertible matrices. The cell equations
from the trailing-minor chart identify the cell with the zero normal section.

This internal result supplies the product coordinates for applying smooth
distribution results on a cell and its transverse derivatives.
