# Schwartz majorants preserving coordinate magnitudes

This internal helper specializes the smooth majorant construction of
`SchwartzRapidMajorant` to finite rows of real and complex coordinates.
It is derived from Mathlib's explicit inner product bump and finite products,
rather than a separate assertion from the literature.

`radialBump` uses `ContDiffBumpBase.ofInnerProductSpace` at outer radius two.
Its value depends only on the norm, it is nonnegative, it equals one on the
closed unit ball, and nonvanishing implies norm less than two. The explicit
base's smoothness proves smoothness of this fixed-radius bump.

`coordinateBump` multiplies these bumps over all rows and real and complex
coordinates. Finite products preserve smoothness and nonnegativity. On the
unit ball every factor is one. Nonvanishing forces each coordinate norm to
be less than two, so the support lies in the closed ball of radius two for
the product supremum norm. Finite dimensionality makes that ball compact,
which gives compact support and hence a Schwartz map.

`exists_coordinate_schwartz_majorant` applies the prescribed-bump majorant
theorem to this bump. Equality of every real and complex coordinate magnitude
is preserved under all real dilations, so the resulting nonnegative Schwartz
majorant has the same symmetry. The input family need not be continuous.
This helper does not yet assert an adelic gauge or any integral estimate.
