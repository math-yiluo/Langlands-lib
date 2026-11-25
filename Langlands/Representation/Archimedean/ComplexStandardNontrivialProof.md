# Proof of `ComplexStandardNontrivialStatement`

Module: `Langlands.Representation.Archimedean.ComplexStandardNontrivialProof` (namespace
`Langlands.Archimedean`).

Main theorem: `Langlands.Archimedean.complexStandardNontrivial :
Langlands.Archimedean.ComplexStandardNontrivialStatement`.

## What is proved

`ComplexStandardNontrivialStatement` (statement NZ) is stated in
`Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction`:

  for every `n : ℕ` and every list `ds : List ComplexCharacterData` with `ds.length = n`, the
  space `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` is `Nontrivial`.

Here `complexStandardModule n ds = principalSeries ℂ n (complexPositionCharacter ds)` consists
of the real-`C^∞` functions `f` on `GL_n(ℂ)` (smooth for the Library's `matrixModel ℂ n`) with

  `f(diag(a) u g) = principalSeriesCharacter ℂ n (complexPositionCharacter ds) a · f(g)`

for `a : Fin n → ℂˣ`, `u` upper unipotent and `g ∈ GL_n(ℂ)`, and `kFiniteFunctions` keeps those
whose right translates by `U(n) = unitaryCompact ℂ n` span a finite-dimensional space.

The proof writes down one element `f` of this space with `f(1) = 1`, so `f ≠ 0`. The length
hypothesis `ds.length = n` is not used: the construction works for every list, with the
trivial character at positions past the end of the list (as in `complexPositionCharacter`).

## The function

Write `Y` for an `n × n` complex matrix. For `k : ℕ` let `LowIdx n k` be the indices `i : Fin n`
with `k ≤ i`, and put

- `lowMinor k Y = D_k(Y) = det (Y i j)_{i, j ≥ k}`, the bottom-right minor;
- `lowGram k Y = G_k(Y) = det (R Rᴴ)` with `R = (Y i j)_{i ≥ k, j}` the rows `i ≥ k` of `Y`
  (a Gram determinant).

Let `m i` and `t i` be the weight and the exponent of the character at position `i`
(`posWeight ds i`, `posExponent ds i`, both `0` past the end), so that, by
`ComplexCharacterData.character_eq`, the character at position `i` is
`z ↦ (z/‖z‖)^(m i) ‖z‖^(2 t i)`. Put `W i = t i + ((n - 1)/2 - i)` (`nzFullExponent`), and take
successive differences (`tele`):

  `μ 0 = m 0`, `μ k = m k - m (k-1)`; `w 0 = W 0`, `w k = W k - W (k-1)`

(`nzWeight`, `nzExponent`). With `p_k = max(μ k, 0)`, `q_k = max(-μ k, 0)` and
`σ_k = w k - (p_k + q_k)/2`, the factor of the `k`-th minor is (`nzFactor`, `minorFactor`)

  `F_k(Y) = D_k(Y)^(p_k) · conj(D_k(Y))^(q_k) · exp(σ_k · log Re G_k(Y))`

and the function is (`nzFunction`)

  `f(Y) = ∏_{k < n} F_k(Y)`, and on `GL_n(ℂ)`, `f(g) = f(g as a matrix)`.

## Proof route, section by section

### `K`-finite functions form a subalgebra (section `Subalgebra`)

For a group `G` and a subgroup `K`, `kFiniteSubalgebra K` is the Library's
`kFiniteVectors (Whittaker.rightTranslation ℂ G) K` packaged as a subalgebra of `G → ℂ`.
Closure under products: right translation is multiplicative (`rightTranslation_mul_apply`), so
the span of the translates of `f h` lies in the product of the spans for `f` and `h`, which is
finitely generated (`Submodule.FG.mul`). Constants are invariant. Two criteria follow:
a `K`-invariant function is `K`-finite (`mem_kFiniteSubalgebra_of_invariant`), and so is a
function whose translates lie in a fixed finite-dimensional space
(`mem_kFiniteSubalgebra_of_le`). `det_mem_subalgebra`: the determinant of a matrix with
entries in a subalgebra lies in it (`RingHom.map_det` for the inclusion).

### Minors and Gram determinants (section `Minors`)

- For `b` upper triangular, the rows `i ≥ k` of `b Y` are `b' R` with `b'` the bottom-right
  block of `b` (`lowRows_mul_of_isUpperTriangular`: the entries `b i l` with `l < k ≤ i`
  vanish). Since `det b' = ∏_{i ≥ k} b i i` (`det_lowBlock_of_isUpperTriangular`):
  - `lowMinor_mul_of_isUpperTriangular`: `D_k(b Y) = (∏_{i ≥ k} b i i) · D_k(Y)`;
  - `lowGram_mul_of_isUpperTriangular`: `G_k(b Y) = |∏_{i ≥ k} b i i|² · G_k(Y)`.
- `lowGram_mul_unitary`: for `U` unitary, `G_k(Y U) = G_k(Y)`, because `(R U)(R U)ᴴ = R Rᴴ`.
- `lowMinor_one`, `lowGram_one`: `D_k(1) = G_k(1) = 1`.
- `lowGram_pos`: for `Y` invertible, `R` has injective `vecMul` (its rows are rows of `Y`,
  written as `R = S Y` with the row selector `S`, `S Sᴴ = 1`), so `R Rᴴ` is positive definite
  (`Matrix.PosDef.mul_conjTranspose_self`) and `G_k(Y) > 0` (`Matrix.PosDef.det_pos`). Hence
  `Re G_k(Y) > 0` (`lowGram_re_pos`).

### Characters of `ℂˣ` (section `Characters`)

- `unitChar μ w z = (z/‖z‖)^μ · exp(2 w log ‖z‖)`, i.e. `(z/‖z‖)^μ ‖z‖^(2w)`. It is additive
  in `(μ, w)` (`unitChar_add`, `unitChar_sum`) for `z ≠ 0`.
- `polyChar p q σ z = z^p · conj(z)^q · exp(σ log |z|²)`. For `z ≠ 0`,
  `polyChar_eq_unitChar`: `polyChar p q σ z = unitChar (p - q) ((p + q)/2 + σ) z`, from
  `z = ‖z‖ (z/‖z‖)` and `conj z = ‖z‖ (z/‖z‖)⁻¹`. It is multiplicative on nonzero
  arguments (`polyChar_mul`, `polyChar_prod`).
- `tele m` is the sequence of successive differences, and `∑_{k ≤ i} tele m k = m i`
  (`sum_range_tele`, and `sum_fin_le_tele` over `Fin n`).
- `complexPositionCharacter_eq`: the character at position `i` is
  `unitChar (posWeight ds i) (posExponent ds i)` (by `character_eq`, writing
  `‖z‖^(2t)` as `exp(2t log ‖z‖)` with `Complex.cpow_def_of_ne_zero`; past the end both
  sides are `1`).
- `principalSeriesCharacter_eq`: with `finrank ℝ ℂ = 2`,
  `principalSeriesCharacter ℂ n (complexPositionCharacter ds) a =
   ∏_i unitChar (m i) (t i + ((n - 1)/2 - i)) (a i)`.

### Transformation under upper triangular matrices (section `Function`)

- `minorFactor_mul_of_isUpperTriangular`: for `b` upper triangular with
  `∏_{i ≥ k} b i i ≠ 0` and `Y` invertible,
  `minorFactor k p q σ (b Y) = polyChar p q σ (∏_{i ≥ k} b i i) · minorFactor k p q σ Y`,
  from the two transformation laws of the section `Minors` and
  `log(|d|² Re G) = log |d|² + log Re G` (both positive).
- `nzFactor_mul_of_isUpperTriangular`: with the choice of `p_k, q_k, σ_k` above
  (`p_k - q_k = μ k` by `Int.toNat_sub_toNat_neg`, and `(p_k + q_k)/2 + σ_k = w k`),
  `polyChar_prod` and `polyChar_eq_unitChar` give
  `F_k(b Y) = (∏_{i ≥ k} unitChar (μ k) (w k) (b i i)) · F_k(Y)` when all `b i i ≠ 0`.
- `prod_lowIdx_prod_unitChar`: exchanging the products
  (`Finset.prod_comm'`), `∏_k ∏_{i ≥ k} unitChar (tele m k) (tele W k) (z i) =
  ∏_i unitChar (∑_{k ≤ i} tele m k) (∑_{k ≤ i} tele W k) (z i) = ∏_i unitChar (m i) (W i) (z i)`
  (`unitChar_sum`, `sum_fin_le_tele`).
- `nzFunction_mul_of_isUpperTriangular`: hence
  `f(b Y) = (∏_i unitChar (m i) (W i) (b i i)) · f(Y)` for `b` upper triangular with nonzero
  diagonal and `Y` invertible.

### Smoothness (section `Smooth`)

Matrix entries and their conjugates are real-smooth (continuous ℝ-linear maps), so `D_k` and
`G_k` (polynomials in them, `contDiff_det_of_entries` via `Matrix.det_apply'`) are smooth on
all matrices. On the invertible matrices `Re G_k > 0`, so `log Re G_k` and its exponential are
smooth there (`ContDiffOn.log`, `ContDiffOn.cexp`). Thus `contDiffOn_nzFunction`: `f` is
`C^∞` on `{Y | IsUnit Y}`. The Library lemma `contMDiff_of_contDiffOn`
(`Langlands.Representation.Archimedean.PrincipalSeriesStability`) turns this into the
`ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞` clause of `principalSeries`.

### `U(n)`-finiteness (section `KFinite`)

- `entryFn_mem`: for a ring homomorphism `h : ℂ →+* ℂ` (here the identity or complex
  conjugation), `g ↦ h(g a b)` is `U(n)`-finite: its right translate by `k` is
  `∑_l h(k l b) · (g ↦ h(g a l))`, in the span of the `n` functions `g ↦ h(g a l)`.
- `minorFn_mem`: `g ↦ h(D_k(g))` is the determinant of the matrix of functions
  `g ↦ h(g i j)` (`i, j ≥ k`), so it is `U(n)`-finite by `det_mem_subalgebra`.
- `expFn_mem`: `g ↦ exp(σ log Re G_k(g))` is right `U(n)`-invariant by `lowGram_mul_unitary`,
  hence `U(n)`-finite.
- `nzFunction_mem`: `f` is a product of powers of these functions, so it lies in
  `kFiniteSubalgebra (unitaryCompact ℂ n)` by the subalgebra closure properties.

### Assembly (`complexStandardNontrivial`)

Given `n` and `ds`, let `f(g) = nzFunction n ds g`.

1. Smoothness: `contMDiff_of_contDiffOn (contDiffOn_nzFunction ds)`.
2. Transformation law: for `a`, `u` upper unipotent and `g`, the matrix
   `b = diag(a) u` is upper triangular (`Matrix.blockTriangular_diagonal`, `.mul`) with
   diagonal entries `b i i = a i ≠ 0`. By `nzFunction_mul_of_isUpperTriangular` (with `g`
   invertible) and `principalSeriesCharacter_eq`,
   `f(diag(a) u g) = principalSeriesCharacter ℂ n (complexPositionCharacter ds) a · f(g)`.
3. `U(n)`-finiteness: `nzFunction_mem ds`.

So `f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`. Finally
`f(1) = 1`, since `D_k(1) = G_k(1) = 1`, `log 1 = 0` and `1^p = 1`; so `f ≠ 0` (compare values
at `1`), which gives `Nontrivial`.

## Provenance

NZ is an internal statement of the proof of `ComplexStandardSurjectionInjectiveStatement` (see the Markdown of
`ComplexStandardSurjectionInjectiveReduction`), needed because irreducibility in the Library
includes nontriviality. The proof is an explicit elementary construction written for this
module: products of powers of the bottom-right minors, their conjugates and real powers of
Gram determinants are the classical way to produce vectors in principal series of `GL_n`
transforming under the Borel subgroup by a prescribed character; no external source is used
in the Lean proof.

## Lean notes

- `set_option backward.isDefEq.respectTransparency false` is set for the module, as in the
  Library's `GKModule`: the manifold structure on the units of the matrix ring needs
  unfolding through the normed-ring instances of matrices.
- The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
