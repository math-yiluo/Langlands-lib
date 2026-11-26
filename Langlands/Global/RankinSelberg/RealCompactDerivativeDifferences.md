# Compact right differences of real principal-series sections from right derivatives

Fix a rank `n = r + 1`. For a matrix direction `Y` the Library's right derivative
`rightDerivative Y u (g) = d/dt u(g exp(tY))|_{t=0}` of a smooth function `u` on `GL_n(ℝ)`
is iterated along words by `RealLocalWhittaker.iteratedRightDerivative`.

## Definitions

* `elem (a, b)` is the elementary matrix with entry `1` at `(a, b)`; `word w` is the list of
  elementary matrices of a list `w` of index pairs.
* `entryNorm Y = Σ_{a,b} |Y_{ab}|`, and `wordNorm Ys` is the product of the entry norms of
  the letters of `Ys`.
* `WordBound m u R`: for every elementary word `w` of length at most `m` and every orthogonal
  matrix `x`, `‖iteratedRightDerivative (word w) u (x)‖ ≤ R`. In particular `R ≥ 0`
  (`WordBound.nonneg`); `WordBound.mono` weakens it.

## Linear algebra of right derivatives

* `rightDerivative_eq_sum`, `iter_append_eq_sum`: right derivatives of smooth functions are
  linear in the direction, so the innermost letter of a word expands in elementary matrices.
* `norm_iter_le`: under `WordBound (length Ys) u R`, every word `Ys` of arbitrary matrices has
  iterated derivative at most `wordNorm Ys · R` on `O(n)`.
* `norm_iter_sub_le`: if two words `Ys`, `Zs` (after a common prefix `Ws`) differ letterwise
  by at most `δ` in entry norm, with all letters of entry norm at most `β ≥ 1`, then their
  iterated derivatives on `O(n)` differ by at most a constant multiple of `δ R` (telescoping
  over the letters, using multilinearity).
* `iter_translate`: right translation by `h` turns the word `Ys` into the conjugated word
  `h⁻¹ Y h`, evaluated at `g h`.
* `iter_mem_principalSeries`: iterated right derivatives stay in the principal series
  (`rightDerivative_mem_principalSeries`).

## One step

`exists_oneStep`: for every block list `ds` there is `C ≥ 0` such that every `u` in the
principal series of `ds` with `WordBound 1 u R` satisfies

`‖u(x k) - u(x)‖ ≤ C ‖k - 1‖ R` for all orthogonal `x`, `k`.

If `‖k - 1‖ ≥ 1/2` this follows from `‖u‖ ≤ R` on `O(n)`. Otherwise follow the straight path
`γ(t) = x (1 + t (k - 1))`, which stays in `GL_n(ℝ)` with matrix norms of `γ(t)` and `γ(t)⁻¹`
bounded by `2n` (Neumann series). The derivative of `u ∘ γ` is a right derivative of `u` at
`γ(t)` in a direction of norm at most `2 ‖k - 1‖`. The first derivatives of `u` in the
elementary directions are again principal-series sections bounded by `R` on `O(n)`, so the
Library's height bound `realPrincipalSeriesHeight` bounds them on the path by `A R H₀^N`, since
the matrix height of `γ(t)` is at most a constant `H₀`. The mean value inequality gives the
estimate.

## Differences of all orders

`exists_wordBound_difference`: for every `ds` and `m` there is `C ≥ 0` such that, for `u` in
the principal series of `ds` with `WordBound (m + 1) u R` and orthogonal `k`, the difference
`g ↦ u(g k) - u(g)` satisfies `WordBound m` with constant `C ‖k - 1‖ R`. By `iter_translate`,
a word of the difference at `x` is the conjugated word at `x k` minus the word at `x`; the
conjugated letters differ from the elementary ones by at most a constant times `‖k - 1‖`
(`norm_iter_sub_le`), and the remaining difference of one fixed word between `x k` and `x` is
the one-step estimate applied to its iterated derivative.

`RealCompactDerivativeDifferencesStatement`: for every rank `r + 1`, block list `ds` and order
`J` there is `C ≥ 0` such that every standard vector `f` with `WordBound J f R` satisfies
`CompactDifferenceBound J f (C R)` (`RealCompactDifferences`). `realCompactDerivativeDifferences`
proves it (`exists_compactDifferenceBound`) by induction on the list of compact moves, each move
lowering the word order by one and contributing its displacement `‖k - 1‖`.

On the compact Banach completion of the standard module, the compact values of the derivative
coordinates of a smooth vector are exactly these iterated right derivatives
(`derivativeCLM_compactEval` in `RealExactStandardEvaluation`). This module therefore turns
finitely many derivative-word norms into the compact difference bounds of
`RealWhittakerFiniteOrder`; `RealExactStandardEvaluation` uses it in that way.
