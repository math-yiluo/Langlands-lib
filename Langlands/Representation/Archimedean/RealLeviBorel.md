# The `O(N)`-integral in coordinates of the opposite unipotent radical of the Borel subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviBorel`.

This is a
helper module of the proof of `Langlands.Archimedean.RealLeviParabolicIntegrationStatement` (see
`RealLeviParabolicIntegration.md`). It states no proposition for publication; it proves lemmas
only. The proof is internal and follows no literature source; it is an induction on `N` from the
Library's maximal-parabolic integration formula. Unprefixed names below are in the namespace
`Langlands.Archimedean.RealLeviBorel`. `iota`, `iotaGL`, `Jmat`, `JGL`, `chartGL`, `natural`,
`leviSlice`, `chartConstant` and `integral_eq_chart` are from the Library module
`MaximalParabolicIntegration`. `CoordC`, `lowerC` (module `RealLeviChartIntegrable`), `lowerCGL`
and `integrable_comp_lowerCGL` (module `RealLeviTwoBlock`) are described in the Markdown files of
those helper modules. `O(N)` carries the Haar probability measure `haarK N` (Library
`RealPrincipalSeriesDuality`).

## The coordinates of `N̄_B`

- `vcl N : Fin N → ℕ` is the identity position function `p ↦ p`, and `vcl_monotone N` says that it
  is monotone. For this block function every block has size `1`: the coordinates `CoordC (vcl N)`
  are the pairs `(p, q)` with `q < p`, and `lowerC (vcl N) Y = n̄_B(Y)` is the lower unitriangular
  matrix with the entries `Y_{pq}` below the diagonal. `CoordC (vcl 0)` is empty.
- `toCoordB m : Fin m ⊕ CoordC (vcl m) → CoordC (vcl (m + 1))` sends `j` to the entry `(m, j)` of
  the last row and a coordinate `(p, q)` of `vcl m` to the same pair in `Fin (m + 1)`.
  `toCoordB_bijective`: this is a bijection.
- `embedB m : (Fin m → ℝ) × (CoordC (vcl m) → ℝ) ≃ᵐ (CoordC (vcl (m + 1)) → ℝ)` puts the last row
  `v` and the coordinates `Y'` together (`embedB_inl`, `embedB_inr`). It is
  `MeasurableEquiv.sumPiEquivProdPi` (inverse) followed by `MeasurableEquiv.piCongrLeft` along
  `toCoordB`. `measurePreserving_embedB`: it preserves Lebesgue measure
  (`volume_measurePreserving_sumPiEquivProdPi_symm`, `measurePreserving_piCongrLeft`).

## `ι(n̄_B(Y')) J(v, 1) = n̄_B(Y)`

Here `ι(A) = diag(A, 1)` and `J(r)` is the identity matrix with its last row replaced by `r`.

- `iota_mul_Jmat_castSucc`, `iota_mul_Jmat_castSucc_last`, `iota_mul_Jmat_last`: the entries of
  `ι(A) J(r)` are `A_{ij}` for `i, j < m`, `0` at `(i, m)` for `i < m`, and `r_j` in the last row.
- `iota_lowerC_mul_Jmat`: `ι(n̄_B(Y')) J(v, 1) = n̄_B(embedB m (v, Y'))`, by comparing entries.
- `iotaGL_lowerCGL_mul_chartGL`: the same identity in `GL_{m+1}(ℝ)`, with `chartGL v = J(v, 1)`.

## The integration formula

`integral_eq_borel`: for every `N` there is `C_N > 0` such that

`∫_{O(N)} F(κ) dκ = C_N ∫_{CoordC (vcl N) → ℝ} F(n̄_B(Y)) dY`

for every smooth `F : GL_N(ℝ) → ℂ` with `F(diag(t) u g) = δ_B(t) F(g)`
(`MaximalParabolicIntegration.IsModulusCovariant`).

The proof is induction on `N`.

- `N = 0`: both sides are `F(1)`, with `C_0 = 1`. `O(0)` is a probability space and the coordinate
  space is a point of volume `1`.
- `N = m + 1`: the Library's `integral_eq_chart` gives
  `∫_{O(m+1)} F = c_m ∫_v natural F (chartGL v) dv` with `c_m = chartConstant m > 0`. Here
  `natural F x = ∫_{O(m)} F(ι(k) x) dk`. Because `|det k| = 1` (`abs_det_unitary`), the integrand is
  the Library's Levi slice `leviSlice F (chartGL v)` (`F(ι(g) y) |det g|^{-1}`) on `O(m)`. That
  slice is smooth and modulus covariant for `GL_m(ℝ)` (`contMDiff_leviSlice`,
  `leviSlice_covariant`). So the induction hypothesis gives
  `natural F (chartGL v) = C_m ∫_{Y'} leviSlice F (chartGL v) (n̄_B(Y'))`. Since
  `det n̄_B(Y') = 1`, this is `C_m ∫_{Y'} F(n̄_B(embedB m (v, Y')))`, by
  `iotaGL_lowerCGL_mul_chartGL`. The function `Y ↦ F(n̄_B(Y))` is integrable
  (`integrable_comp_lowerCGL` with `κ = 1`). Fubini (`integral_prod`) and the measure preserving
  map `embedB m` turn the iterated integral over `(v, Y')` into `∫_Y F(n̄_B(Y)) dY`. Hence
  `C_{m+1} = c_m C_m`.
