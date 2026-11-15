# Rank-one Jacquet functionals for an adjacent swap

Module `Langlands.Representation.Archimedean.ComplexSwapJacquetProof`, namespace
`Langlands.Archimedean.ComplexSwapJacquet`. This internal helper module for
`ComplexStandardPermutationStatement` has no literature source. It imports
`ComplexSwapJacquetFunctional`, `ComplexSwapJacquetLie` and `ComplexPermutationSwap` (where
`ComplexPermutation.SwapJacquetStatement`, `listExponent`, `listWeight` and `length_swap` are
defined).

## Declarations

* `chartLieFacts ds hn i j hj : ChartLieFacts ds hn i j hj` holds for every list `ds` and
  adjacent positions `i`, `j = i + 1`. Each field is the corresponding pointwise formula of
  `ComplexSwapJacquetLie`: `rightDerivative_chart_single_ij`,
  `rightDerivative_chart_strictUpper`, `rightDerivative_chart_diag_other`,
  `rightDerivative_chart_diag_j`, `rightDerivative_chart_diag_i`,
  `rightDerivative_one_strictUpper` and `rightDerivative_one_diag`. The first one needs only
  the smoothness `hf.1` of `f`.
* `swapJacquet_of_nonvanishing hnz : ComplexPermutation.SwapJacquetStatement`. The hypothesis
  `hnz` covers every `pre`, `post`, `d`, `e`, `n` with
  `hn : (pre ++ d :: e :: post).length = n`, and positions `i`, `j : Fin n` with
  `i = |pre|`, `j = i + 1`, `0 ≤ Re(t_d - t_e)` and `(l_d, t_d) ≠ (l_e, t_e)`. For these it
  asks for `c : ℂ` and a `U(n)`-finite `f` in the standard module of `pre ++ d :: e :: post`
  with `∫ integrand (pre ++ d :: e :: post) hn i j hj c f z dz ≠ 0`.

  Proof: given the data of `SwapJacquetStatement`, set `i = |pre|` and `j = |pre| + 1`, both
  less than `n` because the list has length `|pre| + 2 + |post|`. Then apply
  `exists_swapJacquetFunctional` with `chartLieFacts` and `hnz`. Its exponents
  `2 t^{es}_k + (n - 1) - 2k` and `i l^{es}_k` for `es = pre ++ e :: d :: post` are the
  bodies of `listExponent n es _` and `listWeight n es _`, so they match by definitional
  unfolding.
