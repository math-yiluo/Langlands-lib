# The twist `g ↦ w₀ (gᵀ)⁻¹` of `GL_n(ℝ)` and principal series

Lean module: `Langlands.Representation.Archimedean.RealReverseTwist`.

Worker 5 wrote this module for Task 7069 (`79f2a631-6cbb-4805-97c7-163e69df5de3`), the proof of
`RealStandardIrreducibleCriterionStatement`. It is a helper for the reversal statement for
character lists with ties (`RealCharacterReverseKernel`). It is the real analogue of the module
`ComplexReverseTwist` in Worker 5677's complex reversal argument (Task 7064), with the same
twist `g ↦ w₀ (gᵀ)⁻¹`. Over `ℝ` the automorphism `g ↦ (gᵀ)⁻¹` is the identity on `O(n)`, which
simplifies the Haar-measure step.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, `O(n)` is `unitaryCompact ℝ n` with the
Haar probability measure `RealPrincipalSeriesDuality.haarK n`. `R(g)` is
`Whittaker.rightTranslation ℂ _ g`, so `R(g) f (x) = f(x g)`, and
`rightDerivative (matrixModel ℝ n) Y f` is the right derivative `(d/ds) f(g exp(sY))` at `s = 0`.
`principalSeries ℝ n χ` is the Library's smooth principal series of the characters
`χ_0, …, χ_{n−1}` of `ℝˣ`: smooth `f` with
`f(diag(a) u g) = principalSeriesCharacter ℝ n χ a · f(g)` for `u` upper unipotent, where
`principalSeriesCharacter ℝ n χ a = ∏_j χ_j(a_j) |a_j|^{(n−1)/2 − j}`. `Fin.rev j = n − 1 − j`.

Declarations without a prefix are in the namespace `Langlands.Archimedean.RealReverseTwist`.
There is no statement (`def … : Prop`) in this module; it contains definitions and theorems only.

## Definitions

* `w0Mat n`: the antidiagonal permutation matrix, `w0Mat n i j = 1` if `i = Fin.rev j`, else
  `0`. `w0GL n`: the same matrix as an element of `GL_n(ℝ)` (it is its own inverse).
* `transposeGL g = gᵀ`, as an element of `GL_n(ℝ)` (its inverse is `(g⁻¹)ᵀ`).
* `conjAut : GL_n(ℝ) →* GL_n(ℝ)`, `conjAut g = (gᵀ)⁻¹`.
* `twist g = w₀ · conjAut g = w₀ (gᵀ)⁻¹`.
* `twistLin n : (GL_n(ℝ) → ℂ) →ₗ[ℂ] (GL_n(ℝ) → ℂ)`, `twistLin n f = f ∘ twist` (pullback along
  the twist).

## Results

### `w₀`

* `w0Mat_apply`, `w0Mat_mul_apply` (`(w₀ M)_{ij} = M_{rev i, j}`), `mul_w0Mat_apply`
  (`(M w₀)_{ij} = M_{i, rev j}`), `w0Mat_mul_mul_w0Mat_apply`
  (`(w₀ M w₀)_{ij} = M_{rev i, rev j}`), `w0Mat_mul_self` (`w₀² = 1`), `w0Mat_transpose`
  (`w₀ᵀ = w₀`).
* `w0GL_val`, `w0GL_mul_self`, `w0GL_inv` (`w₀⁻¹ = w₀`), `w0GL_mem` (`w₀ ∈ O(n)`).

### Transposition and `conjAut`

* `transposeGL_val`, `transposeGL_inv_val`, `transposeGL_mul` (`(gh)ᵀ = hᵀ gᵀ`),
  `transposeGL_one`, `transposeGL_transposeGL`, `transposeGL_inv` (`(g⁻¹)ᵀ = (gᵀ)⁻¹`),
  `transposeGL_w0GL` (`w₀ᵀ = w₀`), `transposeGL_of_mem` (`kᵀ = k⁻¹` for `k ∈ O(n)`).
* `conjAut_apply`, `conjAut_conjAut` (involution), `conjAut_transposeGL`
  (`conjAut (gᵀ) = g⁻¹`), `conjAut_w0GL` (`conjAut w₀ = w₀`), `conjAut_of_mem`
  (`conjAut k = k` for `k ∈ O(n)`).
* `conjAut_matrixExpUnit`: `conjAut (exp(sY)) = exp(s(−Yᵀ))` (`matrixExpUnit`).

### The twist

* `twist_mul`: `twist (g h) = twist g · conjAut h`.
* `twist_twist`: `twist (twist g) = g`.
* `twist_one`: `twist 1 = w₀`.
* `twist_mul_transposeGL`: `twist (g hᵀ) = twist g · h⁻¹`.
* `twist_of_mem`: `twist k = w₀ k` for `k ∈ O(n)`.
* `integral_mul_inv_eq_twist` (the twisted pairing identity): for all functions `a, b` on
  `GL_n(ℝ)` and `g ∈ GL_n(ℝ)`,

  `∫_{O(n)} a(κ g⁻¹) b(κ) dκ = ∫_{O(n)} a(twist(κ gᵀ)) b(twist κ) dκ`.

### Twisting functions and principal series

* `twistLin_apply` (`twistLin n f g = f (twist g)`), `twistLin_twistLin` (involution).
* `contMDiff_twistLin`: `twistLin n` preserves smoothness on `GL_n(ℝ)`.
* `w0_conj_diagonal`: `w₀ conjAut(diag(a)) w₀ = diag(i ↦ (a_{rev i})⁻¹)`.
* `w0_conj_upperUnipotent`: `w₀ conjAut(u) w₀` is upper unipotent for `u` upper unipotent.
* `twist_diagonal_mul`: `twist(diag(a) u g) = diag(i ↦ (a_{rev i})⁻¹) · u' · twist g` with
  `u' = w₀ conjAut(u) w₀` upper unipotent.
* `norm_inv_cpow`: `‖z⁻¹‖^{−c} = ‖z‖^c` for `z ∈ ℝˣ`, `c ∈ ℂ`.
* `principalSeriesCharacter_rev_inv`: if `χ'_j(z) = χ_{rev j}(z⁻¹)` for all `j : Fin n` and
  `z ∈ ℝˣ`, then `principalSeriesCharacter ℝ n χ (i ↦ (a_{rev i})⁻¹) =
  principalSeriesCharacter ℝ n χ' a`.
* `twistLin_mem_principalSeries`: under the same hypothesis on `χ'`, `f ∈ principalSeries ℝ n χ`
  implies `twistLin n f ∈ principalSeries ℝ n χ'`.
* `rightTranslation_twistLin`: for `k ∈ O(n)`, `R(k) (twistLin n f) = twistLin n (R(k) f)`.
* `twistLin_mem_kFiniteFunctions`: under the same hypothesis on `χ'`, `twistLin n` maps the
  `O(n)`-finite functions of `principalSeries ℝ n χ` into those of `principalSeries ℝ n χ'`.
* `rightDerivative_twistLin`: for smooth `f`,
  `rightDerivative Y (twistLin n f) = twistLin n (rightDerivative (−Yᵀ) f)`.

Provenance. Derived, internal infrastructure: elementary matrix identities and the invariance of
Haar measure. The fact that `g ↦ w₀ (gᵀ)⁻¹` carries `I(χ)` to `I(w₀χ⁻¹)` is standard (it underlies
the contragredient description of standard modules of `GL_n`); the module makes no claim beyond
the Lean statements.

## Proof

The `w₀` identities are entrywise computations (`Finset.sum_eq_single (Fin.rev i)`). `w0GL_mem`:
`w₀ᵀ w₀ = w₀² = 1`. The transposition identities are `Matrix.transpose_mul` and its relatives;
`transposeGL_of_mem` is `kᵀ k = 1` on `O(n)` (`transpose_mul_self_of_mem`). `conjAut` is a
monoid homomorphism because `((gh)ᵀ)⁻¹ = (gᵀ)⁻¹(hᵀ)⁻¹`. `conjAut_matrixExpUnit`:
`(exp(−sY))ᵀ = exp(−sYᵀ)` (`Matrix.exp_transpose`).

`twist_twist`: `twist (twist g) = w₀ conjAut(w₀) conjAut(conjAut g) = w₀ w₀ g = g`.
`twist_mul_transposeGL`: `conjAut(hᵀ) = h⁻¹`.

`integral_mul_inv_eq_twist`. For `κ ∈ O(n)`, `twist(κ gᵀ) = twist(κ) g⁻¹ = w₀ κ g⁻¹` and
`twist κ = w₀ κ`. So the right-hand integrand is the left-hand integrand at `w₀ κ`. Left
invariance of the Haar measure on `O(n)` (`integral_mul_left_eq_self`, with the local Borel
instance `borelSpaceK_tw`) gives equality.

`contMDiff_twistLin`. Use `contMDiff_of_contDiffOn` with the extension
`ψ(y) = unitsExtension f (w₀ (Ring.inverse y)ᵀ)` on the open set of invertible matrices: matrix
inversion is smooth there (`contDiffAt_ringInverse`), `y ↦ w₀ yᵀ` is continuous linear, and
`unitsExtension f` is smooth on units (`contDiffOn_unitsExtension`). At `y = g` it equals
`f(twist g)` (`unitsExtension_val`).

`w0_conj_diagonal` and `w0_conj_upperUnipotent`: `conjAut(M) = (M⁻¹)ᵀ`, and conjugation by `w₀`
reverses both indices. `(diag(a)⁻¹)ᵀ = diag(a⁻¹)`, and for `u` upper unipotent `(u⁻¹)ᵀ` is lower
unipotent, so its `w₀`-conjugate is upper unipotent with unit diagonal. `twist_diagonal_mul`
inserts `w₀ w₀ = 1` between the factors of `conjAut(diag(a) u g)`.

`principalSeriesCharacter_rev_inv`. Reindex the product by `Fin.revPerm`. At index `j` the factor
`χ_{rev j}((a_j)⁻¹) · |(a_j)⁻¹|^{(n−1)/2 − (n−1−j)}` equals
`χ'_j(a_j) · |a_j|^{(n−1)/2 − j}`, using `(n−1)/2 − (n−1−j) = −((n−1)/2 − j)` and
`norm_inv_cpow`.

`twistLin_mem_principalSeries`. Smoothness is `contMDiff_twistLin`. For equivariance,
`twist(diag(a) u g) = diag(a_{rev}⁻¹) u' twist(g)`, so
`f(twist(diag(a) u g)) = principalSeriesCharacter χ (a_{rev}⁻¹) · f(twist g)`, which is
`principalSeriesCharacter χ' a · f(twist g)`.

`rightTranslation_twistLin`: `twist(g k) = twist(g) conjAut(k) = twist(g) k` for `k ∈ O(n)`.
`twistLin_mem_kFiniteFunctions`: the span of the `O(n)`-translates of `twistLin n f` is contained
in the image under `twistLin n` of the span of the translates of `f`, which is finite-dimensional.

`rightDerivative_twistLin`. Both sides are derivatives at `s = 0`
(`hasDerivAt_mul_matrixExpUnit_smul`) of the same function of `s`:
`f(twist(g exp(sY))) = f(twist(g) conjAut(exp(sY))) = f(twist(g) exp(s(−Yᵀ)))`.
Uniqueness of derivatives gives equality.
