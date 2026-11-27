# Heights of positive torus points in simple-root and central coordinates

Module `Langlands.Global.AdelicUniformTemperednessHeights`, namespace
`Langlands.Global.StandardParabolicFamily`.

For a standard parabolic family `𝓕` with a coordinate frame `Fr : TorusFrame 𝓕` and a matrix
representation `rho : MatrixRepresentation G (Fin N)` with `N > 0`, write `‖u‖` for the norm of
the coordinates `Fr.crd u` of a positive point `u` of the maximal split torus `T`.

## Results

- `TorusFrame.exists_coordinate_characters`: finitely many characters `χ_k` of `T` span the
  rational character space. The values `ℓ(χ_k)` and the coordinates of `ℓ` control each other
  linearly. The `χ_k` are the coordinate characters of a splitting of `T`
  (`coordinateCharacter`, `character_eq_sum_coordinateCharacter`), and the comparison constant
  comes from the operator norms of the linear isomorphism between the two coordinate systems.
- `adelicHeight_torus`: the height of `u` for `i ≫ rho` equals the height of its image in
  `G(𝔸)`.
- `TorusFrame.exists_height_le` (**upper bound**): there are `C ≥ 1` and `r ≥ 0` with
  `‖torusPoint u‖_rho ≤ C e^{r ‖u‖}` for every positive `u`. This is
  `adelicPositiveTorusLogHeightBound` applied to the spanning characters.
- `TorusFrame.exists_crd_le_log_height` (**lower bound**): if `rho` is a closed embedding, there
  are `A, B ≥ 0` with `‖u‖ ≤ A log ‖torusPoint u‖_rho + B` for every positive `u`. For each `χ_k`, `exists_characterNorm_le`
  (applied to the closed embedding `i ≫ rho`) gives `|χ_k(u)|^{±1} ≤ C_k ‖u‖_rho^{e_k}`, so
  `|log |χ_k(u)|| ≤ log C_k + e_k log ‖u‖_rho`. The coordinates are then controlled by
  `exists_coordinate_characters`.

## Source

These are the standard comparisons between the height on `G(𝔸)` and the logarithm on the split
torus (Mœglin–Waldspurger 1995, I.2.2), used in the uniform temperedness criterion to convert
powers of `1 + ‖log a‖` into powers of the logarithmic height `σ`.
