# Bump functions along a standard parabolic subgroup

Lean module: `Langlands.Representation.Archimedean.RealLeviBump`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It is
the second of three modules (`RealLeviPairing`, `RealLeviBump`, `RealLeviNonvanishing`) for the
nonvanishing step of the single-shot Langlands-quotient argument. The entry statement of the
three modules is `RealLeviNonvanishingStatement` (see `RealLeviNonvanishing.md`). This module
states no `Prop`-valued statement of its own. No literature statement is claimed and nothing is
cited; the provenance is internal ("derived"). Unprefixed names below are in the namespace
`Langlands.Archimedean.RealLeviBump`.

## Notation

* Library module `PrincipalSeriesGramFormula` (namespace `GramFormula`): for `l : ℕ` and an
  `n × n` matrix `Z`, `padded l Z` agrees with `Z` on the rows and columns `≥ l` and with the
  identity matrix elsewhere, so `m_l(Z) = det (padded l Z)` is the minor of `Z` on the rows and
  columns `≥ l`. `gram l Z = det (paddedGram l Z)`, where `paddedGram l Z` agrees with `Z Zᵀ` on
  the rows and columns `≥ l` and with the identity elsewhere: `G_l(Z) = gram l Z` is the Gram
  determinant of the rows `≥ l` of `Z`.
* `RealLeviChartIntegralStatement`: block sizes `sz : Fin c → ℕ`, `N = ∑_i sz_i`, first block
  positions `l_i = start sz i = sz_0 + ⋯ + sz_{i-1}`, `cls sz p` the block of a position,
  `Coord sz` and `lower sz X = n̄(X)` as in `RealLeviPairing.md`.
* `RealLeviGeometry`: `BlockZero sz k` means that `k` has no entries between different blocks.
  `scaleCoord sz s X` multiplies the coordinate `(p, q)` of `X` by `s^{cls q} / s^{cls p}`; it
  is the coordinate vector of the conjugate of `n̄(X)` by the diagonal matrix with entries
  `s^{cls p}` (`lower_mul_diagonal`).

## Definitions

* `bumpFactor l Z = m_l(Z)² / G_l(Z)`.
* `omega sz Z = ω(Z) = ∏_{i < c} bumpFactor l_i Z`. (The factor with `l_0 = 0` equals `1` on
  invertible matrices; this is not needed.)
* `beta sz X = β(X) = ω(n̄(X))`.
* `entryMatrix n`: the `n × n` matrix of coordinate polynomials `X_{(p,q)}` in
  `MvPolynomial (Fin n × Fin n) ℂ`.
* `omegaPoly sz = ∏_i m_{l_i}(entryMatrix N)²`.

## Results

**Padded matrices and Gram determinants** (section `Pad`).

* `padded_mul`: `padded l (W Z) = padded l W · padded l Z` if `W_{pr} Z_{rq} = 0` whenever
  `p, q ≥ l > r`.
* `padded_one`, `padded_transpose`, `padded_map` (compatibility with ring homomorphisms).
* `gram_mul_left`: `G_l(W Z) = m_l(W)² G_l(Z)` if `W` has no entries in the rows `≥ l` and the
  columns `< l`.
* `gram_mul_orth`: `G_l(Z k) = G_l(Z)` for orthogonal `k`. `gram_of_orth`: `G_l(k) = 1` for
  orthogonal `k`.
* `det_padded_sq`: `m_l(k)² = 1` for orthogonal `k` with no entries in the rows `≥ l` and the
  columns `< l`. `det_padded_ne_zero`: then `m_l(k) ≠ 0`.
* `bumpFactor_mul_left` (invariance under such `W` with `m_l(W) ≠ 0`), `bumpFactor_mul_right`
  (invariance under orthogonal `k` that is block diagonal for the splitting at `l`),
  `bumpFactor_of_orth` (`= m_l(k)²`), `bumpFactor_of_lower` (`= G_l(L)⁻¹` for lower unipotent `L`).
* `one_lt_det_one_add`: `det(1 + Y Yᵀ) > 1` for a nonzero real square matrix `Y` (`Y Yᵀ` is
  positive semidefinite and nonzero, so its eigenvalues are `≥ 0`, not all `0`).

**The function `ω`** (section `Levi`).

* `start_mono`, `start_le_iff` (`l_i ≤ p ↔ i ≤ cls sz p`), `blockUpper_of_blockZero`,
  `blockLower_of_blockZero`: a `BlockZero` matrix has no entries between the rows `≥ l_i` and the
  columns `< l_i`, nor between the rows `< l_i` and the columns `≥ l_i`.
* `omega_mul_upper`: `ω(b Z) = ω(Z)` for upper triangular `b` with nonzero diagonal.
* `omega_mul_left`, `omega_mul_right`: `ω(k Z) = ω(Z) = ω(Z k)` for orthogonal `BlockZero`
  matrices `k`, i.e. elements of `∏_i O(sz_i)` embedded block diagonally.
* `omega_of_orth`: `ω(k) = ∏_i m_{l_i}(k)²` for orthogonal `k`.
* `beta_eq`: `β(X) = ∏_i G_{l_i}(n̄(X))⁻¹`.
* `eval_omegaPoly`: evaluating `omegaPoly sz` at the entries of a real matrix `k` gives
  `∏_i m_{l_i}(k)²`.

**Multiplication by powers of `ω`** (section `Bump`).

* `exists_bump`: let `χ` be a signed power character (`IsSignedPower χ e`, Library module
  `RealStrictCharacterLanglandsQuotient`) and `f` an `O(N)`-finite vector of
  `principalSeries ℝ N χ`. For every `m : ℕ` there is an `O(N)`-finite vector `f'` of the same
  principal series with `f'(g) = ω(g)^m f(g)` for all `g ∈ GL_N(ℝ)`. Proof: on `O(N)`, `f` is a
  polynomial `P` in the matrix entries (Library
  `OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors`). The function
  `φ = (omegaPoly^m · P)` on `O(N)` equals `ω^m f` there (`eval_omegaPoly`, `omega_of_orth`). Its
  right translates span a finite-dimensional space (Library
  `TranslateFinite.finiteDimensional_span_eval`), and it transforms under the sign reflections
  like `f` (`omega_mul_upper` for diagonal sign matrices). The Library extension
  `PrincipalSeriesExtension.extension_mem_kFiniteFunctions` extends `φ` to an `O(N)`-finite
  vector `f'` of the principal series. By the Iwasawa decomposition `g = a u k` and
  `omega_mul_upper`, `f'(g) = ω(g)^m f(g)`.
* `exists_bump_standard`: if `realRank ds = N` and the exponents of `ds` decrease strictly from
  a block of `Q` to any later block, then for an `O(N)`-finite vector `f` of
  `realStandardModule N ds` the vector `f'` of `exists_bump` lies in the standard module again.
  Proof: the strict decrease puts every induction block of `ds` inside one block of `Q`
  (`slots_cls_eq`), so `ω` is invariant under the block rotations of the induction blocks, and
  the vanishing of the block coefficients of modes `|j| < M` passes from `f` to `ω^m f`
  (`RealLeviModes.window_of_mem_standard` and `mem_kFin_standard_of_window`).

**The function `β`** (section `Beta`).

* `continuous_beta`, `beta_pos`, `beta_le_one` (each `G_{l_i}(n̄(X)) ≥ 1`), `beta_zero`
  (`β(0) = 1`).
* `beta_le_beta_scale`: `β(X) ≤ β(scaleCoord sz s X)` for `s ≥ 1` (Gram monotonicity of
  `RealLeviGeometry`).
* `scaleCoord_one`, `norm_scaleCoord_le` (`‖scaleCoord sz s X‖ ≤ ‖X‖ / s` for `s ≥ 1`),
  `continuousOn_scaleCoord`.
* `beta_lt_one`: `β(Y) < 1` for `Y ≠ 0`. Proof: choose a nonzero entry `Y_{pq}` with `p` maximal
  and let `l = l_i` for the block `i` of `p`. On the rows and columns `≥ l`, `n̄(Y)` is the
  identity, so `G_l(n̄(Y)) = det(1 + C Cᵀ)` for the lower left corner `C ≠ 0`
  (`gram_of_block_one`), which is `> 1` by `one_lt_det_one_add`. The other factors are `≤ 1`.
* `exists_gap`: for every `δ > 0` there is `q < 1` with `β(X) ≤ q` whenever `‖X‖ ≥ δ`. Proof:
  by the intermediate value theorem on `s ↦ ‖scaleCoord sz s X‖` over `[1, ‖X‖/δ]`, some `Y` with
  `‖Y‖ = δ` has `β(X) ≤ β(Y)` (`beta_le_beta_scale`). On the compact sphere of radius `δ`, `β`
  attains its maximum at some `Y_0 ≠ 0`, and `q = β(Y_0) < 1` by `beta_lt_one`.
