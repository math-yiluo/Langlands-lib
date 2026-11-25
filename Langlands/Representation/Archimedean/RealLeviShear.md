# Block lower unitriangular times opposite-radical coordinates as coordinates of `N̄_B`

Lean module: `Langlands.Representation.Archimedean.RealLeviShear`.

This is a
helper module of the proof of `Langlands.Archimedean.RealLeviParabolicIntegrationStatement` (see
`RealLeviParabolicIntegration.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names below are in the
namespace `Langlands.Archimedean.RealLeviShear`. The names used from the helper modules are
described in their Markdown files: `CoordC` and `lowerC` (`RealLeviChartIntegrable`), `lowerCGL`
(`RealLeviTwoBlock`), `vcl` (`RealLeviBorel`), and `CoordM`, `lowerM` and `lowerMGL`
(`RealLeviLeviBorel`).

For a monotone block function `cl : Fin N → ι` into a linear order, write `n̄(X) = lowerC cl X`
(coordinates `X : CoordC cl → ℝ` below the blocks), `m(Z) = lowerM cl Z` (coordinates
`Z : CoordM cl → ℝ` inside the blocks, below the diagonal), and `n̄_B(Y) = lowerC (vcl N) Y` (all
coordinates below the diagonal). The module shows that `(Z, X) ↦ m(Z) n̄(X)`, written in the
coordinates of `n̄_B`, is a measure preserving map.

## The strictly lower part of `n̄(X)` (section `Strict`)

- `strictC cl X = n̄(X) − 1`: the matrix with the entries `X (p, q)` at the coordinates and `0`
  elsewhere (`lowerC_eq_strictC_add_one`).
- `strictC_add`, `strictC_smul`: `X ↦ strictC cl X` is linear. `continuous_strictC`.
- `strictC_single`: `strictC cl` of the standard basis vector at `y = (p₀, q₀)` is the matrix unit
  at `(p₀, q₀)`.

## Products with block diagonal lower unitriangular matrices (section `Product`)

- `lowerM_self`: the diagonal entries of `m(Z)` are `1`. `lowerM_eq_zero_of_ne`: `m(Z)_{pr} = 0`
  if `cl p ≠ cl r`.
- `lowerM_mul_strictC_eq_zero`: `(m(Z) strictC(X))_{pq} = 0` unless `cl q < cl p`. Indeed
  `m(Z)_{pr} ≠ 0` needs `cl r = cl p`, and `strictC(X)_{rq} ≠ 0` needs `cl q < cl r`.
- `lowerM_mul_lowerC`: `m(Z) n̄(X) = m(Z) strictC(X) + m(Z)`.

So the entries of `m(Z) n̄(X)` are the entries of `m(Z)` inside the blocks and the entries of
`m(Z) strictC(X)` below the blocks.

## The shear (section `Shear`)

- `shearL cl Z : (CoordC cl → ℝ) →ₗ[ℝ] (CoordC cl → ℝ)` is the linear map
  `X ↦ ((m(Z) strictC(X))_{pq})_{(p, q)}` (`shearL_apply`).
- `toMatrix'_shearL`: its matrix has the entry `m(Z)_{p p'}` at `((p, q), (p', q'))` if `q = q'`,
  and `0` otherwise.
- `det_shearL`: `det (shearL cl Z) = 1`. Order the coordinates by their row `p`, in the reverse
  order (`OrderDual`). The matrix is block triangular for this order (`Matrix.BlockTriangular`),
  because `m(Z)` is lower triangular. A diagonal block (fixed row `p`) is the identity matrix,
  because `m(Z)_{pp} = 1`. So the determinant is `1` (`Matrix.BlockTriangular.det`).
- `map_shearL`: `shearL cl Z` preserves Lebesgue measure
  (`Real.map_linearMap_volume_pi_eq_smul_volume_pi`).
- `continuous_shearL`: `(Z, X) ↦ shearL cl Z X` is continuous.

## Splitting the coordinates of `N̄_B` (section `Split`)

- `toCoordS hcl : CoordM cl ⊕ CoordC cl → CoordC (vcl N)` sends a pair `(p, q)` inside a block or
  below the blocks to the same pair. For a pair below the blocks, `cl q < cl p` gives `q < p`
  because `cl` is monotone. `toCoordS_bijective`: it is a bijection, since every pair `q < p`
  satisfies either `cl p = cl q` or `cl q < cl p`.
- `embedS hcl : (CoordM cl → ℝ) × (CoordC cl → ℝ) ≃ᵐ (CoordC (vcl N) → ℝ)` puts the two families
  of coordinates together (`embedS_inl`, `embedS_inr`). `measurePreserving_embedS`: it preserves
  Lebesgue measure (`volume_measurePreserving_sumPiEquivProdPi_symm`,
  `measurePreserving_piCongrLeft`).

## The factorization (section `Factor`)

- `shear hcl (Z, X) = embedS hcl (Z, shearL cl Z X)`.
- `measurePreserving_shear`: `shear hcl` maps the product of the Lebesgue measures to Lebesgue
  measure. The map `(Z, X) ↦ (Z, shearL cl Z X)` preserves the product measure by
  `MeasurePreserving.skew_product`, since each `shearL cl Z` preserves Lebesgue measure. Then
  compose with `embedS`.
- `lowerC_shear`: `n̄_B(shear hcl (Z, X)) = m(Z) n̄(X)`, entry by entry: above the diagonal both
  sides vanish, on the diagonal they are `1`, inside the blocks the entry is `Z (p, q)`
  (`lowerM_mul_strictC_eq_zero`), and below the blocks it is `shearL cl Z X (p, q)`.
- `lowerCGL_shear`: the same identity in `GL_N(ℝ)`,
  `lowerCGL (vcl_monotone N) (shear hcl (Z, X)) = lowerMGL cl Z * lowerCGL hcl X`.
