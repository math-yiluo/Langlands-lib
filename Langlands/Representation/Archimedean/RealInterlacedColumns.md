# Interlaced induction blocks: column functions and their expansions

Lean module: `Langlands.Representation.Archimedean.RealInterlacedColumns`, namespace
`Langlands.Archimedean.RealInterlacedJacquet`.

Second of the six modules that prove `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`
(see `RealInterlacedMirror.md`). It imports `RealInterlacedJacquet` and uses its expansions
`IsExpansion` and `HasExpTop`. It defines the functions on matrices from which the test vectors of
the proof are built, and computes their expansions along the block rotations `r_b(t)`. The notation
is that of `RealInterlacedJacquet.md`. `MF n` is the ring of functions
`Matrix (Fin n) (Fin n) ℝ → ℂ`.

## Column combinations (section Columns)

* `colv u i X = (X u)_i = Σ_c X_{ic} u_c` for a complex vector `u`. Since `r_b(t)` acts on rows,
  `colv_rot_ia`, `colv_rot_ib` and `colv_rot_of_ne` say that the pair
  `((X u)_b, (X u)_{b+1})` is rotated by `t` and the other entries are unchanged.
  `colv_diag`: a diagonal matrix on the left scales the entries. `colv_one`: `colv u i 1 = u_i`.
* `yZ hb u = (X u)_b + i (X u)_{b+1}` and `yZb hb u = (X u)_b - i (X u)_{b+1}`. Under `r_b(t)`
  they are multiplied by `e^{it}` and `e^{-it}` (`yZ_rot`, `yZb_rot`). They are unchanged by the
  rotations of a disjoint block (`yZ_rot_of_disjoint`, `yZb_rot_of_disjoint`).

## Continuous `O(n)`-finite functions (section Finite)

* `PF n` is the subalgebra of `MF n` of continuous functions whose restriction to `O(n)` is
  `O(n)`-finite under translations (the Library's `IsTranslateFinite`).
* `entry_mem_PF`, `colv_mem_PF`, `det_mem_PF`: matrix entries, column combinations and the
  determinant lie in `PF n`. `comp_left_mem_PF`: so does `X ↦ H(m X)` for `m ∈ O(n)` and `H ∈ PF n`.

## The special orthogonal group (section Special)

* `SOset n` is `SO(n)` as a subset of `GL_n(ℝ)`: elements of `O(n)` of determinant `1`.
* `det_sq_of_mem`, `det_blockRotation`, `rot_mul_mem_SOset`, `one_mem_SOset`,
  `blockRotation_mem_SOset`: `det g = ±1` on `O(n)`, `det r_b(t) = 1`, and `SO(n)` is stable under
  the block rotations.

The proof tracks functions on `SO(n)` only. The values of a Frobenius function at `κ` depend only
on the orbit `r_b(t) κ`, which stays in the component of `κ`.

## Steps of multipliers on `SO(n)` (section Steps)

* `eq_zero_of_modes`: if `f(r_b(t) κ) = H(r_b(t) κ)` for all `t`, `H` has an expansion along `b`,
  and all `Φ^{(b)}_j(f)(κ)` vanish, then `f(κ) = 0` (the expansion is a finite Fourier series).
* `exists_step` (**one step of a multiplier**): if `f = H` on `SO(n)` with `H ∈ S` and
  `HasExpTop b N S T`, then `κ ↦ (2π)⁻¹ Σᶠ_j μ_j Φ^{(b)}_j(f)(κ)` agrees on `SO(n)` with some
  `H' ∈ S`, namely `H' = Σ_k μ_{k-N} P_k` (`finsum_of_expansion`).
* `blockFourierCoefficient_eq_of_expansion`: in the same situation, for `κ ∈ SO(n)`,
  `Φ^{(b)}_j(f)(κ) = 2π P_{j+N}(κ)` if `0 ≤ j + N ≤ 2N`, and `0` otherwise.

## Spans of column functions (section Spans)

* `Ly u` is the span of the column functions `colv u i`, `i < n`. It contains `yZ hb u` and
  `yZb hb u`.
* `quad_coeff_mem`, `exists_gen`: a generator in the form `cos t A + sin t B + C` with `A, B, C`
  in a span has an expansion of order `1` with coefficients in the span.
* `hasExpTop_Ly`: `HasExpTop b 1 (Ly u) (span {yZ hb u})`. The top coefficient of a column
  function is a multiple of `yZ hb u`.
* `hasExpTop_mono`: enlarging `T`. `span_singleton_pow_mul`:
  `span{a}^m · span{c}^k = span{a^m c^k}`.

## Four coordinates (section Four)

On `4 × 4` matrices let `y = X u` and `z = X u'` be two complex column combinations.

* `pl u u' i j = y_i z_j - y_j z_i` are the Plücker coordinates of `y ∧ z`.
* The self-dual combinations are `w₁ = p₀₁ + p₂₃`, `w₂ = p₀₂ - p₁₃` and `w₃ = p₀₃ + p₁₂`. Let
  `ν₊ = w₂ + i w₃` (`nup`), `ν₋ = w₂ - i w₃` (`num`) and `w₊ = w₁ + i w₂` (`wp`).
* `h40`, `h41`, `h42` are the three blocks `0, 1, 2` of `GL₄`. `colv_rot0`, `colv_rot1` and
  `colv_rot2` are the column laws for them, and `sin_sq_add_cos_sq_complex` is a helper.
* `w_rot0`, `w_rot2`: under `r₀(t)` and under `r₂(t)`, `w₁` is fixed and `(w₂, w₃)` is rotated by
  `t`. `w_rot1`: under `r₁(t)`, `(w₁, w₂)` is rotated by `t` and `w₃` is fixed. Proof: expand the
  Plücker coordinates and use `sin² + cos² = 1`.
* `nup_rot0`, `num_rot0`, `nup_rot2`, `num_rot2`: `ν₊` and `ν₋` have the weights `1` and `-1`
  under the rotations of the blocks `0` and `2`.
* `colv_diag4`: diagonal matrices scale the entries.
* `Lw u u'` is the span of `w₁, w₂, w₃`. It contains `ν₊` and `ν₋`.
* `hasExpTop_Lw1`: `HasExpTop 1 1 (Lw u u') (span {w₊})`. `hasExpTop_Lw0` and `hasExpTop_Lw2`:
  `Lw u u'` has expansions of order `1` along the blocks `0` and `2` (top coefficient
  unrestricted).
* `Sm u u' r m = Ly u ^ r · Lw u u' ^ m` is the span of products of `r` column functions of `u` and
  `m` self-dual coordinates.
* `hasExpTop_Sm1`: `HasExpTop 1 (r + m) (Sm u u' r m) (span {yZ h41 u ^ r · w₊ ^ m})`. So along
  the middle block every function of `Sm` has modes `|j| ≤ r + m`, and its top mode `r + m` is a
  multiple of the single function `yZ h41 u ^ r · w₊ ^ m`. `hasExpTop_Sm0`, `hasExpTop_Sm2`: the
  same along the blocks `0` and `2` without the restriction on the top coefficient.
* `pl_mem_PF`, `w1_mem_PF`, `w2_mem_PF`, `w3_mem_PF`: these functions lie in `PF 4`.

The module compiles with no errors or warnings.

## Provenance

Internal to the proof of `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`. The self-dual combinations are the standard decomposition
`Λ²ℂ⁴ = Λ²₊ ⊕ Λ²₋` under `SO(4)`, restricted here to what the proof uses: the three block
rotations act on `L_w` as computed above. The consequence used later is that the middle block
has a one-dimensional space of top modes on `Sm`. Everything else is elementary linear algebra
and Fourier analysis on the circle.
