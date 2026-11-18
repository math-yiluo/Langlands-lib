# The integral over a block orthogonal group in block lower unitriangular coordinates

Lean module: `Langlands.Representation.Archimedean.RealLeviLeviBorel`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`). It is a
helper module of the proof of `Langlands.Archimedean.RealLeviParabolicIntegrationStatement` (see
`RealLeviParabolicIntegration.md`). It states no proposition for publication; it proves lemmas
only. The proof is internal and follows no literature source. Unprefixed names below are in the
namespace `Langlands.Archimedean.RealLeviLeviBorel`. The names used from the helper modules
are described in their Markdown files: `CoordC`, `lowerC`, `clR` and `exists_first_block`
(`RealLeviChartIntegrable`); `dg`, `dgGL`, `sliceL`, `sliceR`, `lowerCGL`, `exists_bound`,
`norm_le_gram_inv` and `integrable_prod_gram_inv` (`RealLeviTwoBlock`); `vcl` and
`integral_eq_borel` (`RealLeviBorel`); `Kc`, `μc`, `dgK` and `integral_Kc_eq`
(`RealLeviBlockHaar`). `gram` is the Library's `GramFormula.gram`, and `δ_B` is the modulus
character of the upper triangular Borel subgroup.

## Block diagonal lower unitriangular matrices (section `Chart`)

For a block function `cl : Fin N → ι` into a linear order:

- `CoordM cl` is the subtype of pairs `(p, q)` with `cl p = cl q` and `q < p`: the coordinates of
  the lower unitriangular group of the Levi subgroup.
- `lowerM cl Z` is the matrix with the entry `Z (p, q)` at the coordinates, `1` on the diagonal
  and `0` elsewhere. `lowerM_isLowerTriangular`, `det_lowerM` (`det = 1`), `isUnit_lowerM`.
- `lowerMGL cl Z` is `lowerM cl Z` as an element of `GL_N(ℝ)` (`lowerMGL_val`).
- `gram_lowerM_pos`: its Gram determinants are positive (Library `GramFormula.gram_pos`).
- `continuous_lowerM`: `Z ↦ lowerM cl Z` is continuous.

## Splitting off the first block (section `Peel`)

Here `cl : Fin (a + M) → ι` is constant `c₀` on the first `a` positions (`h1`), and `cl > c₀` on
the last `M` positions (`h2`).

- `toCoordM h1 : CoordC (vcl a) ⊕ CoordM (clR cl) → CoordM cl` maps a coordinate `(p, q)` of the
  lower unitriangular group of `GL_a` to `(p, q)`, and a coordinate `(p, q)` of `clR cl` to
  `(a + p, a + q)`. `toCoordM_bijective`: it is a bijection, because no coordinate of `cl` joins
  the first block to a later block.
- `embedM h1 h2 : (CoordC (vcl a) → ℝ) × (CoordM (clR cl) → ℝ) ≃ᵐ (CoordM cl → ℝ)` puts the
  coordinates together (`embedM_inl`, `embedM_inr`). `measurePreserving_embedM`: it preserves
  Lebesgue measure.
- `lowerM_embedM`: `lowerM cl (embedM (Z₁, Z')) = diag(n̄_B(Z₁), lowerM (clR cl) Z')`, and
  `lowerMGL_embedM` is the same identity in `GL_{a+M}(ℝ)`.

## Gram determinants of block diagonal matrices

`prod_gram_inv_dg`: if `det B = 1`, then
`∏_{l < a+M} G_l(diag(A, B))^{-1} = ∏_{i < a} G_i(A)^{-1} · ∏_{r < M} G_r(B)^{-1}`. This follows
from `gram_dg_of_le` and `gram_dg_add` (module `RealLeviTwoBlock`), since `det(B Bᵀ) = 1`.

## The integration formula

`leviBorel`: for every `N`, every monotone `cl : Fin N → ι`:

1. `Z ↦ ∏_{l < N} G_l(lowerM cl Z)^{-1}` is integrable on `CoordM cl → ℝ`;
2. there is `C > 0` with `∫_{Kc cl} F(k) dμc cl = C ∫_{CoordM cl → ℝ} F(lowerM cl Z) dZ` for every
   smooth `F : GL_N(ℝ) → ℂ` with `F(diag(t) u g) = δ_B(t) F(g)`
   (`MaximalParabolicIntegration.IsModulusCovariant`).

The proof is strong induction on `N`.

- `N = 0`: the coordinate space is a point of volume `1`, both sides are `F(1)`, and `C = 1`.
- `N > 0`: `exists_first_block` gives the size `a ≥ 1` of the first block, and `N = a + M`. The
  induction hypothesis for `clR cl` (with `M < N`) gives the integrability `hIR` and the constant
  `C_R`, and `integral_eq_borel a` gives the constant `C_a`. The new constant is `C_a C_R`.
  - Integrability (part 1). Composed with `embedM`, the integrand is the product of
    `∏_i G_i(n̄_B(Z₁))^{-1}` and `∏_r G_r(lowerM Z')^{-1}` (`lowerM_embedM`,
    `prod_gram_inv_dg`). Both factors are integrable (`integrable_prod_gram_inv`, `hIR`), so their
    product is integrable on the product space (`Integrable.mul_prod`).
  - The formula (part 2). Let `B` bound `‖F‖` on `O(N)` (`exists_bound`). By `integral_Kc_eq`,
    `∫_{Kc cl} F = ∫_{O(a)} ∫_{Kc (clR cl)} F(diag(k₁, k₂)) dk₂ dk₁`. Exchange the two integrals
    (`integral_integral_swap`; the integrand is continuous on a compact space).
  - For fixed `k₂`, the integrand in `k₁` is the Levi slice `sliceL F (diag(1, k₂))`, because
    `|det k₁| = 1`. The slice is smooth and modulus covariant for `GL_a(ℝ)`, so
    `integral_eq_borel` turns the `O(a)`-integral into `C_a ∫_{Z₁} F(diag(n̄_B(Z₁), k₂)) dZ₁`.
  - Exchange the integrals over `k₂` and `Z₁` again. The integrand is bounded by
    `B · c' · ∏_i G_i(n̄_B(Z₁))^{-1}` with the constant `c' = ∏_r G_r(1)^{-1}`. This follows from
    `norm_le_gram_inv` with `y = diag(n̄_B(Z₁), 1)` and `κ = diag(1, k₂)`, and
    `prod_gram_inv_dg`. The bound is integrable on `Kc (clR cl) × (CoordC (vcl a) → ℝ)`.
  - For fixed `Z₁`, the integrand in `k₂` is the Levi slice `sliceR F (diag(n̄_B(Z₁), 1))`,
    because `|det k₂| = 1`. The induction hypothesis turns the `Kc (clR cl)`-integral into
    `C_R ∫_{Z'} F(diag(n̄_B(Z₁), lowerM Z')) dZ' = C_R ∫_{Z'} F(lowerM cl (embedM (Z₁, Z'))) dZ'`
    (`lowerMGL_embedM`).
  - `Z ↦ F(lowerM cl Z)` is integrable: it is continuous and bounded by
    `B ∏_l G_l(lowerM cl Z)^{-1}` (`norm_le_gram_inv` with `κ = 1`; part 1). Fubini
    (`integral_prod`) and the measure preserving `embedM` turn the iterated integral over
    `(Z₁, Z')` into `∫_Z F(lowerM cl Z) dZ`.
