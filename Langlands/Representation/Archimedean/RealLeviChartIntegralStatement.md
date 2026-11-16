# Integrability of the Gram bound on the opposite unipotent radical of a parabolic subgroup of `GL_N(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealLeviChartIntegralStatement`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
states one proposition, `RealLeviChartIntegrableStatement`, and does not prove it. The module also
defines the coordinates of a standard parabolic subgroup and proves a few elementary lemmas about
them. The proposition generalizes the published `RealBlockChartIntegrableStatement` (module
`RealBlockChartIntegralStatement`) from the maximal parabolic subgroup `P_{a,k}` to an arbitrary
standard parabolic subgroup `Q`, in the special case that the problem needs: the exponents are
tied inside each block of `Q`. See "Use" below.

## Definitions

All are in the namespace `Langlands.Archimedean.RealLeviChart`. The data are a number `c` of blocks
and the block sizes `sz : Fin c → ℕ`. The matrix size is `N = ∑ i, sz i`, and the positions are
`Fin (∑ i, sz i)`.

* `cls sz p : Fin c` is the block that contains the position `p`, and `pos sz i a` is the position
  of the index `a < sz i` inside the block `i`. Both are defined through Mathlib's
  `finSigmaFinEquiv : (Σ i : Fin c, Fin (sz i)) ≃ Fin (∑ i, sz i)`. This equivalence lists the
  pairs `(i, a)` in lexicographic order, so the blocks are consecutive intervals of positions.
* `start sz i = ∑_{k < i} sz k` (a natural number) is the first position of the block `i`.
* Lemmas: `cls_pos` (`cls (pos i a) = i`), `pos_cls` (every position is `pos (cls p) a` for some
  `a`), `val_pos` (`pos i a = start i + a` as natural numbers), `start_succ_le`
  (`start i + sz i ≤ start j` for `i < j`) and `lt_of_cls_lt` (`cls p < cls q → p < q`: an earlier
  block comes before a later one).
* `Coord sz` is the subtype of pairs `(p, q)` of positions with `cls q < cls p`. These are the
  matrix entries strictly below the diagonal blocks, i.e. the coordinates of the opposite unipotent
  radical `N̄_Q` of the upper block triangular parabolic subgroup `Q` with blocks of sizes `sz`.
* `lower sz X` for `X : Coord sz → ℝ` is the matrix `n̄(X)`. Its entry `(p, q)` is `X (p, q)` if
  `cls q < cls p`, `1` if `p = q`, and `0` otherwise.
* `lower_isLowerTriangular`, `lower_apply_self` and `det_lower` show that `n̄(X)` is lower
  triangular with diagonal entries `1`, so its determinant is `1`. `lowerGL sz X` is `n̄(X)` as
  an element of `GL_N(ℝ) = Langlands.GeneralLinear N ℝ`, and `lowerGL_val` says its underlying
  matrix is `lower sz X`.

## The statement

`RealLeviChartIntegrableStatement` takes `c`, `sz` and real numbers `γ_l` for the positions `l`.
Assume:

1. `γ_l ≤ −1/2` for every position `l ≥ 1`;
2. `γ_l < −1/2` for every position `l = k + 1` with `cls k < cls l`. These are the first
   positions of the blocks other than the first one, if those blocks are nonempty.

Then the function

`X ↦ ∏_l G_l(n̄(X))^{γ_l}`

is integrable on `Coord sz → ℝ` with the product Lebesgue measure. Here `G_l = GramFormula.gram l`
(module `PrincipalSeriesGramFormula`) is the Gram determinant `det(A Aᵀ)` of the matrix `A` made of
the rows `l, …, N−1` (computed there as the determinant of the Gram matrix of these rows padded by
the identity on the rows `< l`). Powers are real powers (`Real.rpow`).

Edge cases. `G_0(n̄(X)) = det(n̄(X))² = 1`, so `γ_0` plays no role, and the hypotheses do not
constrain it. If `c ≤ 1`, then `Coord sz` is empty, the space `Coord sz → ℝ` is a single point of
measure `1`, and the statement is trivially true. For `c = 2` with blocks of sizes `a` and `k`,
`n̄(X) = [[1, 0], [X, 1]]` and `G_l(n̄(X))` equals `colGram X (l−1)` for `1 ≤ l ≤ a` and
`rowGram X (l−a)` for `a ≤ l < a + k`. These are Schur complement identities, with
`colGram (a−1) = rowGram 0` by Sylvester's determinant identity. Because `rowGram ≥ 1`, the
statement for `c = 2` then follows from `RealBlockChartIntegrableStatement`: the hypotheses give
`γ_l ≤ −1/2` for `1 ≤ l < a`, `γ_a < −1/2` and `γ_l ≤ −1/2` for `l > a`, so every cumulative sum
`∑_{l ≥ j} (ε_l + 1/2)` of that statement is at most `γ_a + 1/2 < 0`.

Only sufficiency is stated. No converse is claimed.

## Provenance

The statement is derived and internal. No literature source is claimed. It is the convergence of
the Jacquet integral over `N̄_Q` of the spherical bound of a real principal series whose exponents
are tied inside the blocks of `Q` and strictly decreasing from block to block. This is a special
case of the Gindikin–Karpelevich convergence of standard intertwining integrals. Take a function
`h` in the smooth principal series of `GL_N(ℝ)` with exponents `s_0, …, s_{N−1}`. On
`n̄(X) O(N)` it is bounded by a constant times `∏_l G_l^{(σ_l − σ_{l−1})/2}`, where
`σ_l = Re s_l + (N−1)/2 − l` (published `ParabolicChartBound` for one row; the general
Iwasawa–Gram formula is in `PrincipalSeriesGramFormula`). At a tie `Re s_{l−1} = Re s_l` the
exponent is `−1/2`. At a strict descent `Re s_{l−1} > Re s_l` it is `< −1/2`.

Intended proof (for a proof task): induction on the number `c` of blocks, in stages. Let `a` be the
size of the first `c − 1` blocks, `k = sz_{c−1}`, and `Q'` the parabolic subgroup of `GL_a(ℝ)` given
by the first `c − 1` blocks. Every element of `N̄_Q` can be written as
`[[n̄', 0], [Y, 1]] = n̄_P(Y n̄'^{-1}) · diag(n̄', 1)` with `n̄' ∈ N̄_{Q'}`. Take the Iwasawa
decomposition `n̄' = b' k'`. Then `|det b'| = 1`, and `diag(b', 1)` can be moved to the left through
`n̄_P` at the cost of the substitution `Y ↦ Y n̄'^{-1} b'`, whose Jacobian is `|det b'|^k = 1`.
Write `E(g) = ∏_l G_l(g)^{γ_l}`. It is left covariant under the upper triangular Borel subgroup
and right `O(N)`-invariant. So the inner integral over `Y` equals
`E(diag(n̄', 1)) · ∫ E(n̄_P(Y)) dY`. The last integral is finite by
`RealBlockChartIntegrableStatement`, because its exponents satisfy the cumulative condition (see
the case `c = 2` above). `E(diag(n̄', 1))` is the same kind of function for `GL_a(ℝ)` and `Q'`. The
induction hypothesis and Tonelli's theorem then conclude.

## Use

In Task 6749 the statement gives the convergence of the integral over `N̄_Q` that defines the
pairing in the single-step Langlands lemma along the parabolic subgroup `Q` whose blocks are the
tie classes of the Langlands order. It also gives integrability of the dominating function in
the limit argument. In the limit argument the exponents become `max(ε_l, −1)`, which still satisfy
the hypotheses.
