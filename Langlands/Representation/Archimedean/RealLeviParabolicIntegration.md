# Proof of the `O(N)`-integral formula in coordinates of a standard parabolic subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviParabolicIntegration`.

This module proves
`Langlands.Archimedean.RealLeviParabolicIntegrationStatement` (module
`RealLeviParabolicIntegrationStatement`; see `RealLeviParabolicIntegrationStatement.md` for the
statement and its notation). The proof is the theorem
`Langlands.Archimedean.realLeviParabolicIntegration`. The proof is internal; it follows no
literature source. Its route is the "intended proof" sketched in the statement's Markdown: Borel
coordinates, Levi-Borel coordinates and a measure preserving shear, with no induction on the
number of blocks.
Unprefixed names below are in the namespace `Langlands.Archimedean.RealLeviParabolicIntegration`.

## Modules used

- Helper modules of this proof (each with its own Markdown file): `RealLeviTwoBlock`
  (two-block Levi embedding, growth bound, integrability along `N̄`), `RealLeviBorel` (the `O(N)`-integral in
  coordinates of `N̄_B`), `RealLeviBlockHaar` (the Haar measure `μc cl` of the block orthogonal
  subgroup `Kc cl`), `RealLeviLeviBorel` (the `Kc cl`-integral in coordinates of the lower
  unitriangular group of the Levi subgroup) and `RealLeviShear` (the shear
  `(Z, X) ↦ m(Z) n̄(X)` in coordinates of `N̄_B`).
- Integrability prerequisites: `RealLeviChartGram` and `RealLeviChartIntegrable`, imported for
  the Gram identities and the proved integrability of the Gram bound.
- `RealLeviGeometry`: the block orthogonal subgroup `blockOrth sz`, the conjugation
  `adCoord k X` of the coordinates (`k n̄(X) kᵀ = n̄(adCoord k X)`), `mul_lowerGL`
  (`g n̄(X) = n̄(Ad(g) X) g` for `g ∈ blockOrth sz`), `measurePreserving_adCoord`, `cls_mono`,
  `BlockZero`, `blockDiagHom_transpose`, `mem_blockOrth_of_mem_unitaryCompact`,
  `blockDiagGL_mem_blockOrth` and `blockDiagGL_mem_unitaryCompact`.
- Library: `RealPrincipalSeriesDuality.haarK` and `measurableSpaceK`,
  `MaximalParabolicIntegration.IsModulusCovariant`, and Mathlib's measure theory.

Notation: `cls sz : Fin N → Fin c` is the block function of the block sizes `sz`
(`N = ∑ i, sz i`), `K_M = ∀ i, O(sz_i)` with the product `μ_K` of the Haar probability measures
`haarK (sz i)`, `diag(κ) = blockDiagGL sz κ`, `n̄(X) = lowerGL sz X` for `X : Coord sz → ℝ`,
`m(Z) = lowerMGL (cls sz) Z` for `Z : CoordM (cls sz) → ℝ`, and `n̄_B(Y)` the lower unitriangular
matrix with the coordinates `Y : CoordC (vcl N) → ℝ`.

## Right translates (section `Translate`)

- `contMDiff_comp_mul_right`: if `F` is smooth on `GL_N(ℝ)`, so is `g ↦ F(g y)`
  (`RealLeviTwoBlock.contMDiff_mul_comp` with `φ` the identity and `c = 1`).
- `isModulusCovariant_comp_mul_right`: if `F(diag(t) u g) = δ_B(t) F(g)`, the right translate
  `g ↦ F(g y)` has the same property.

## The block diagonal decomposition of `Kc (cls sz)` (section `Blocks`)

- `cls_monotone`: `cls sz` is monotone (`cls_mono`).
- `RealLeviTorus.diagBlock g i`: the diagonal block `i` of an `N × N` matrix `g`.
  `RealLeviTorus.blockDiagHom_diagBlock`: a matrix without entries between different blocks (`BlockZero sz g`) is
  the block diagonal matrix of its diagonal blocks. `RealLeviTorus.blockDiagHom_injective`: `blockDiagHom sz` is
  injective. `RealLeviTorus.diagBlock_mul_transpose`: if moreover `g gᵀ = 1`, every diagonal block is orthogonal.
- `exists_blockDiagGL_eq`: every `g ∈ blockOrth sz` is `diag(κ)` for some `κ ∈ K_M`.
- `bd κ = diag(κ)` (an abbreviation). `continuous_bd_val` and `continuous_bd`: `κ ↦ diag(κ)` is
  continuous into the matrices (Mathlib's `Continuous.matrix_blockDiagonal'` and
  `Continuous.matrix_reindex`) and into `GL_N(ℝ)`; the inverse of `diag(κ)` is `diag(κ⁻¹)`.
- `bd_mem_Kc`: `diag(κ) ∈ Kc (cls sz)`. `bdK : K_M →* Kc (cls sz)` is `κ ↦ diag(κ)` (`bdK_val`),
  with `continuous_bdK` and `surjective_bdK` (from `exists_blockDiagGL_eq` and
  `mem_blockOrth_of_mem_unitaryCompact`).
- `map_bdK`: `μc (cls sz)` is the image of `μ_K` under `bdK`. The image is a Haar probability
  measure (`Measure.isHaarMeasure_map_of_isFiniteMeasure`), so `RealLeviBlockHaar.eq_μc`
  applies.
- `integral_pi_mul_eq`: for continuous `f` and every `y`,
  `∫_{K_M} f(diag(κ) y) dμ_K = ∫_{Kc (cls sz)} f(k y) dμc` (`map_bdK`, `integral_map`).

## Moving `diag(κ)` to the left (section `Shift`)

- `continuous_lower_sz`: `X ↦ n̄(X)` is continuous. `lowerGL_eq`: `lowerGL sz X` is
  `lowerCGL (cls_monotone) X` (the same matrix, `Coord sz` being `CoordC (cls sz)`).
- `adBd κ X = adCoord (diag(κ)) X`, the coordinates of `diag(κ) n̄(X) diag(κ)ᵀ`.
  `continuous_adBd`: `(κ, X) ↦ adBd κ X` is continuous. `map_adBd`: for each `κ`, `adBd κ`
  preserves Lebesgue measure (`measurePreserving_adCoord`, since `diag(κ) ∈ blockOrth sz`).
- `shiftAd (κ, X) = (κ, adBd κ X)`. `measurePreserving_shiftAd`: `shiftAd` preserves
  `μ_K ⊗ dX` (`MeasurePreserving.skew_product`).

## The iterated integral (section `Main`)

`integral_integral_eq`: let `C_M` be a constant with
`∫_{Kc (cls sz)} F = C_M ∫_Z F(m(Z)) dZ` for all smooth modulus covariant `F` (hypothesis `hBM`,
supplied by `leviBorel`). Then for smooth modulus covariant `F`,

`∫_{K_M} ∫_X F(n̄(X) diag(κ)) dX dκ = C_M ∫_Y F(n̄_B(Y)) dY`.

Proof, with `g(κ, X) = F(n̄(X) diag(κ))`:

1. `g` is continuous and integrable on `K_M × (Coord sz → ℝ)`. The bound
   `|g(κ, X)| ≤ B ∏_l G_l(n̄(X))^{-1}` comes from `exists_bound` and `norm_le_gram_inv` (since
   `diag(κ) ∈ O(N)` and `G_0(n̄(X)) = 1`), and the right side is integrable
   (`integrable_prod_gram_inv`).
2. Fubini (`integral_prod`) writes the left side as `∫ g d(μ_K ⊗ dX)`. Since `shiftAd` preserves
   `μ_K ⊗ dX`, this equals `∫ g ∘ shiftAd`, and Fubini in the other order (`integral_prod_symm`)
   gives `∫_X ∫_{K_M} g(shiftAd (κ, X)) dκ dX`.
3. `g(shiftAd (κ, X)) = F(n̄(Ad(diag κ) X) diag(κ)) = F(diag(κ) n̄(X))` by `mul_lowerGL`. By
   `integral_pi_mul_eq`, the inner integral is `∫_{Kc (cls sz)} F(k n̄(X)) dk`, and `hBM` applied to
   the right translate `F(· n̄(X))` (section `Translate`) gives `C_M ∫_Z F(m(Z) n̄(X)) dZ`.
4. Let `H(Z, X) = F(m(Z) n̄(X))`. By `lowerCGL_shear`, `H = (Y ↦ F(n̄_B(Y))) ∘ shear`. The function
   `Y ↦ F(n̄_B(Y))` is continuous and integrable (`integrable_comp_lowerCGL` with `κ = 1`), and the
   shear preserves Lebesgue measure (`measurePreserving_shear`). So `H` is integrable, Fubini
   (`integral_prod_symm`) gives `∫_X ∫_Z H = ∫ H d(dZ ⊗ dX)`, and the change of variables by the
   shear gives `∫_Y F(n̄_B(Y)) dY`.

## The theorem

`realLeviParabolicIntegration : RealLeviParabolicIntegrationStatement`. Given `c` and `sz`, let
`C_N > 0` be the constant of `RealLeviBorel.integral_eq_borel N`
(`∫_{O(N)} F = C_N ∫_Y F(n̄_B(Y))`), and let `C_M > 0` be the constant of
`RealLeviLeviBorel.leviBorel N (cls sz)`. Take `C = C_N / C_M > 0`.

1. Integrability: `X ↦ F(n̄(X) diag(κ))` is integrable by `integrable_comp_lowerCGL`, because
   `diag(κ) ∈ O(N)` (`blockDiagGL_mem_unitaryCompact`) and `n̄(X) = lowerCGL (cls_monotone) X`.
2. The formula: `∫_{O(N)} F = C_N ∫_Y F(n̄_B(Y))` and, by `integral_integral_eq`,
   `∫_{K_M} ∫_X F(n̄(X) diag(κ)) = C_M ∫_Y F(n̄_B(Y))`. Hence
   `∫_{O(N)} F = (C_N / C_M) ∫_{K_M} ∫_X F(n̄(X) diag(κ))`.

The constant `C` is not identified explicitly.
