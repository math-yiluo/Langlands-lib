# Cuspidal sums over two-block unipotent radicals

`twoBlockShape hr0 hrm` is the shape `(r, m - r)` with `0 < r < m`. The lemmas
`twoBlockShape_indexEquiv_val` and `twoBlockShape_lt_iff` describe its
numbering. `twoBlockShape_parabolic_ne_top` uses a lower unipotent
transvection outside the upper block parabolic to show properness.
`BlockShape.unipotent_entry` and `twoBlock_unipotent_entry` show that the
entries of an element of the unipotent radical outside the blocks strictly
above the diagonal agree with the identity matrix.

The matrix `cornerMat r Z` keeps the upper right `r × (f - r)` corner of `Z`.
The unipotent `cornerU r Z = 1 + cornerMat r Z` satisfies
`cornerU r Z * cornerU r Z' = cornerU r (Z + Z')`. Every element of the
unipotent radical for `(r, f - r)` is of this form by `eq_cornerU_of_mem`.

For a cuspidal representation `σ` of `GL_f(k)` over a finite field,
`sum_cornerU_eq_zero` gives `∑_Z σ(cornerU r Z) = 0` for `0 < r < f`, with
`Z` ranging over all square matrices. The sum takes values in the vectors
fixed by the unipotent radical, since multiplication by `cornerU r Z₀`
reindexes the sum by `Z ↦ Z₀ + Z`. Cuspidality makes those vectors zero.
`sum_tensorPower_cornerU_eq_zero` applies multilinearity of
`PiTensorProduct.map` to obtain the corresponding sum for the tensor power
at `Pi.mulSingle i₀ (cornerU r Z)`. These vanishing sums apply to the finite
cuspidal data in BK93 (5.5.10)(b).
[Transport to the type](LevelZeroSimpleTypeJacquet.md)
