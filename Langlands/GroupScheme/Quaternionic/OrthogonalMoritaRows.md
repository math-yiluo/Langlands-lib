# Rows in an arbitrary-degree splitting chart

This internal construction supports the all-coefficient Morita representation
comparison. Let `K` and `L` be fields, `D` a division `K`-algebra, and fix an
`L`-algebra equivalence `e : L ⊗[K] D ≃ₐ[L] Matrix (Fin degree) (Fin degree) L`.
For every commutative coefficient ring `R` with compatible `K`- and `L`-algebra
structures, `OrthogonalMorita.rowChart e R` is an `R`-linear equivalence from
`R ⊗[K] (Fin m → D)` to `degree` ordinary rows indexed by
`Fin m × Fin degree`.

The equivalence first distributes the tensor product over the finite row
product, applies the published coefficient splitting map to each entry, then
rearranges the two matrix indices. `rowChart_apply` gives its entries and
`rowChart_tmul` gives its value on pure tensors. The auxiliary
`matrixChartR_apply_tensorMatrix` checks that the two existing entrywise tensor
matrix comparisons agree. `chart_vecMul` expands the finite sums in a block
row product. `rowChart_rightAction` then proves that right multiplication by
an element of `R ⊗[K] Matrix (Fin m) (Fin m) D` becomes right multiplication of
each ordinary row by `DegreeSplitting.matrixChartR e R` of that element.

The provenance is internal: these definitions compose the Library's
`DegreeSplitting` coefficient charts with Mathlib's finite-product tensor
comparison and an explicit rearrangement of indices. The proofs use these
formulas and finite-sum identities, with no restriction on characteristic and
no root, spin, or classification input. This module supplies the row chart;
it does not yet assert existence of a splitting or a group-scheme comparison.
