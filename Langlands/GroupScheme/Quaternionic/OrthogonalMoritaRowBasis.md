# A fixed basis in the split row module

This internal construction composes the coefficient row chart from
`OrthogonalMoritaRows` with a supplied invertible rectangular basis matrix.
The fixed equivalence over `L` sends each row to its product with `P'`, where
`P P' = 1` and `P' P = 1`. Its canonical scalar extension over a compatible
commutative coefficient algebra `R` is the coefficient row chart followed
by multiplication by the entrywise image of `P'`.

The scalar-extension formula is proved on pure tensors, using the published
`rowEquivOver_tmul`, and then by additivity. Combining this formula with the
row-chart multiplication identity proves that right multiplication by a
tensor matrix becomes right multiplication by
`P.map * matrixChartR(a) * P'.map` on each row. This construction assumes
the splitting and the basis matrices; it does not assert their existence.
