# Polar matrices of scalar orthogonal group points

For a field `F`, a form `q` in the scalar-involution quadratic quotient on
`Fin n`, and a commutative `F`-algebra `R`, `scalarMatrixPoint` sends an
`R`-point of the actual isometry group to an invertible `n × n` matrix over
`R`. It is a monoid homomorphism and is injective. It commutes with every
homomorphism of commutative `F`-algebras, including maps between coefficient
algebras with zero divisors.

The matrix `polar q` is symmetric. In characteristic zero, the image of
`scalarMatrixPoint` consists exactly of the units `g` preserving the image
`H` of `polar q` in `R`, with the convention `g H gᵀ = H`.

The construction composes `OrthogonalMorita.isometryAffineUnitsEquiv` with
the inclusion into the units of `R ⊗[F] Matrix (Fin n) (Fin n) F` and
`OrthogonalMatrix.chart` on units. Injectivity and naturality follow from
those of the two comparisons. If `Q` is a representative of `q`, the chart
identifies the isometry defect with `g Q_R gᵀ − Q_R`. Its symmetric part
vanishes exactly when `g` preserves `(Q + Qᵀ)_R`. Since `2` is a unit, the
vanishing symmetric part also forces the defect's diagonal to vanish. This
gives the alternating defect condition and lifts each matrix preserving
`H` back to a coefficient point by the inverse chart and affine equivalence.

This is an internal comparison derived from the Library's affine points,
isometry cut and scalar orthogonal chart. It will be used to compare natural
orthogonal cocycles and their relating cochains with matrix cocycles.
