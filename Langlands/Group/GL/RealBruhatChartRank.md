# Inversion layers in the real Bruhat product chart

`Langlands.GeneralLinear.RealBruhatChartRank.RealBruhatChartRankStatement`
puts the entire invertible target of the real product chart for `w` in the
union of the cell of `w` and the cells of strictly greater inversion count.

The proof writes a matrix in the chart as `b * l * p`, with `b` invertible
upper triangular, `l` lower unitriangular, and `p` the permutation matrix.
Left multiplication by `b` preserves every lower-left corner rank. For
`l * p`, each corner contains a square submatrix indexed by the selected
rows that also arise from the permutation of the selected columns. That
submatrix comes from a principal submatrix of `l` and has determinant one.
Its size is the corner count of `w`, so the corner rank is at least that
count. The cell rank characterization and the strict inversion growth
criterion then give the conclusion.

This internal chart property lets the lower-cell vanishing argument use the
full product chart at each step of the Bruhat filtration.
