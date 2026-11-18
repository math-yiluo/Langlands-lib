# The two-block Levi embedding `GL_a × GL_M → GL_{a+M}` and the growth bound along `N̄`

Lean module: `Langlands.Representation.Archimedean.RealLeviTwoBlock`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`). It is a
helper module of the proof of `Langlands.Archimedean.RealLeviParabolicIntegrationStatement` (see
`RealLeviParabolicIntegration.md`). It states no proposition for publication; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names below are in
the namespace `Langlands.Archimedean.RealLeviTwoBlock`. `gram` is the Library's
`GramFormula.gram`, `IsModulusCovariant` is `MaximalParabolicIntegration.IsModulusCovariant`
(`F(diag(t) u g) = δ_B(t) F(g)` with `δ_B` the modulus character of the upper triangular Borel
subgroup), and `CoordC`, `lowerC`, `padS`, `tm` and `gen` are from the helper modules
`RealLeviChartGram` and `RealLeviChartIntegrable` (see their Markdown files).

## Block diagonal matrices (section `Mat`)

- `dg A B = diag(A, B)`, the `(a + M) × (a + M)` matrix `reindex finSumFinEquiv finSumFinEquiv
  (fromBlocks A 0 0 B)`. Its four blocks are given by the simp lemmas `dg_castAdd_castAdd`,
  `dg_castAdd_natAdd`, `dg_natAdd_castAdd` and `dg_natAdd_natAdd`.
- Algebra: `dg_mul`, `dg_one`, `dg_transpose`, `det_dg` (`det diag(A, B) = det A · det B`),
  `dg_mul_transpose`, `dg_add`, `dg_smul`, and `dg_isUpperTriangular` (upper triangular blocks give
  an upper triangular matrix).
- Gram determinants. `padS_dg_of_le` and `padS_dg_add` compute the padded matrices `padS l` of
  `diag(S, T)`. Hence `gram_dg_of_le`: `G_l(diag(A, B)) = G_l(A) · det(B Bᵀ)` for `l ≤ a`, and
  `gram_dg_add`: `G_{a+r}(diag(A, B)) = G_r(B)`. `RealLeviTorus.gram_zero_eq` gives `G_0(x) = (det x)²`.

## The group homomorphism (section `Group`)

- `dgHom` is `(A, B) ↦ diag(A, B)` as a monoid homomorphism, and
  `dgGL : GL_a(ℝ) × GL_M(ℝ) →* GL_{a+M}(ℝ)` is `Units.map dgHom` composed with
  `MulEquiv.prodUnits.symm`. `dgGL_val` gives its underlying matrix.
- `dgGL_diagonalUnits_left` and `dgGL_diagonalUnits_right`: `diag(diag(t), 1)` and
  `diag(1, diag(t))` are the diagonal matrices of the concatenated entries (`Fin.addCases`).
- `dgGL_mem_upperUnipotent`, `dgGL_mem_unitaryCompact`: `dgGL` maps pairs of upper unipotent
  (orthogonal) matrices to upper unipotent (orthogonal) matrices. `dgGL_injective`.
- `modulusCharacter_addCases_left`: `δ_B^{(a+M)}(t, 1) = δ_B^{(a)}(t) ∏ᵢ |tᵢ|^M`, and
  `modulusCharacter_addCases_right`: `δ_B^{(a+M)}(1, t) = δ_B^{(M)}(t) ∏_r |t_r|^{-a}`
  (Library `modulusCharacter`; the exponent of position `l` is `(n − 1) − 2l`).
- `det_diagonalUnits_mul`: `det(diag(t) u g) = (∏ᵢ tᵢ) det g` for `u` upper unipotent.

## Smoothness and the Levi slices (section `Smooth`)

- `contMDiff_mul_comp`: let `φ : GL_n(ℝ) →* GL_N(ℝ)` be given on matrices by a smooth map `Φ`, let
  `y ∈ GL_N(ℝ)`, and let `c` be smooth on the invertible matrices. If `F` is smooth on `GL_N(ℝ)`,
  then `g ↦ F(φ(g) y) c(g)` is smooth on `GL_n(ℝ)`. The proof uses the Library's extension
  `unitsExtension` of `F` to all matrices (module `PrincipalSeriesStability`), which is smooth on
  the open set of invertible matrices (`contDiffOn_unitsExtension`).
- `contDiffOn_absDet_pow`, `contDiffOn_absDet_pow_inv`: `Y ↦ |det Y|^k` and `Y ↦ |det Y|^{-k}` are
  smooth on the invertible matrices.
- `dgLinL`, `dgLinR` (`A ↦ diag(A, 0)`, `B ↦ diag(0, B)` as linear maps), `contDiff_dg_left` and
  `contDiff_dg_right`: `A ↦ diag(A, B)` and `B ↦ diag(A, B)` are smooth.
- The Levi slices of `F` at `y ∈ GL_{a+M}(ℝ)`: `sliceL F y g = F(diag(g, 1) y) |det g|^{-M}` on
  `GL_a(ℝ)` and `sliceR F y h = F(diag(1, h) y) |det h|^a` on `GL_M(ℝ)`.
  `contMDiff_sliceL`, `contMDiff_sliceR`: they are smooth if `F` is. `sliceL_covariant`,
  `sliceR_covariant`: if `F` is modulus covariant for `GL_{a+M}(ℝ)`, then the slices are modulus
  covariant for `GL_a(ℝ)` and `GL_M(ℝ)`. The proof writes `diag(diag(t) u g, 1)` as
  `diag(t, 1) · diag(u, 1) · diag(g, 1)`, uses the covariance of `F`, and compensates the factor
  `∏ᵢ |tᵢ|^M` (respectively `∏_r |t_r|^{-a}`) of the modulus character by the determinant factor
  (`det_diagonalUnits_mul`).

## Continuity (section `Continuity`)

- `continuous_comp_of_val`: if `F` is smooth on `GL_N(ℝ)` and `x ↦ g(x)` is continuous as a map to
  matrices, then `x ↦ F(g(x))` is continuous.

## Growth bounds (section `Growth`)

- `exists_bound`: a smooth `F` is bounded on the compact group `O(N)`.
- `norm_le_gram_inv`: if `F` is modulus covariant and `‖F‖ ≤ C` on `O(N)`, then
  `‖F(y κ)‖ ≤ C ∏_{l < N} G_l(y)^{-1}` for every `y` with `G_0(y) = (det y)² = 1` and every
  `κ ∈ O(N)`. For `N = 0` this is the bound itself. For `N > 0` it is
  `RealBlockChart.norm_le_gram` (module `RealBlockChartBound`) with the
  exponents `σ_l = (N − 1) − 2l` of the modulus character (Library
  `JacquetLimit.norm_modulusCharacter`). That lemma bounds `‖F(y κ)‖` by
  `C ∏_{l ≥ 1} G_l(y)^{(σ_l − σ_{l−1})/2}`, and here every exponent is `−1`. The factor `l = 0`
  of the product in `norm_le_gram_inv` is `G_0(y)^{-1} = 1`.
- For a monotone block function `cl : Fin N → ι` into a linear order: `lowerCGL hcl X = n̄(X)` as
  an element of `GL_N(ℝ)` (`lowerCGL_val`; invertible by `isUnit_lowerC`), and `gram_zero_lowerC`:
  `G_0(n̄(X)) = 1` because `det n̄(X) = 1`.
- `integrable_prod_gram_inv`: `X ↦ ∏_{l < N} G_l(n̄(X))^{-1}` is integrable on `CoordC cl → ℝ`.
  This is `gen` with every exponent `−1` (finite lower integral), together with the continuity
  and positivity of the integrand (`continuous_prod_gram`, `gram_lowerC_pos`).
- `continuous_lowerCGL_mul`: `X ↦ n̄(X) κ` is continuous.
- `integrable_comp_lowerCGL`: if `F` is smooth and modulus covariant and `κ ∈ O(N)`, then
  `X ↦ F(n̄(X) κ)` is integrable. It is continuous (`continuous_comp_of_val`) and bounded by
  `C ∏_l G_l(n̄(X))^{-1}` (`exists_bound`, `norm_le_gram_inv`), which is integrable.
