# Local solutions of the multiplication equation

`exists_common_chart` puts the two coordinates of a point of `Gl ×_S Gl`
in the same section chart. The proof applies `chartCover` to both points
and intersects the two fibrewise dense opens of section choices. The chosen
open immersions give lifts of scheme-valued points on a neighbourhood.

In a common chart, choose a section `c` satisfying the open conditions for
the two local divisions `xr = c` and `cs = y`. The solutions are given by
`ldiv`, and `mulG (r,s)` solves the equation on the neighbourhood since
`x(rs) = (xr)s = y` by the chart multiplication formulas. Thus
`exists_local_division` supplies local solutions to `xz = y` for points
over any test scheme. This implements the division step of BLR,
*Néron Models*, §5.3 Lemma 8, pp. 127–128, with section choices and local
solutions.
