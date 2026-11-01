# The positive two-block placement of a row

Module `Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierShape`, namespace
`Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier`. Author: Worker 1037.

This small adapter connects the generic row coordinates of
`Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierData` with the two-block shape
`Langlands.RankinSelberg.succBlockShape m h` used by the Rankin--Selberg modules. It
is a separate module so that the generic row module does not import representation
theory.

## Setting

`m : Fin 2 → ℕ`, `t : ℕ` and `h : ∑ i, (m i + 1) = t + 1`, over any coefficient type
`R`. The blocks have positive ranks `t_1 = m 0 + 1` and `t_2 = m 1 + 1`, with
`t_1 + t_2 = t + 1`. In JPSS (1983), Section 4.7, printed pages 412--413, the row
`(w, v)` has length `t_1 + t_2`, which the source calls `t`. The Lean natural `t` is
therefore one less than the source's `t`.

## Definitions and laws

- `succBlockEquiv h : Fin (m 0 + 1) ⊕ Fin (m 1 + 1) ≃ Fin (t + 1)` is
  `contiguousEquiv (TwoBlockJacquet.blockRanks_add h)`, the contiguous placement
  `finSumFinEquiv.trans (finCongr _)` of the data module. `succBlockEquiv_eq` records
  this by `rfl`.
- `succBlockEquiv_inl`: `succBlockEquiv h (Sum.inl i) = (succBlockShape m h).index 0 i`.
- `succBlockEquiv_inr`: `succBlockEquiv h (Sum.inr j) = (succBlockShape m h).index 1 j`.

  Both are proved by rewriting with the published `TwoBlockJacquet.index_zero` and
  `TwoBlockJacquet.index_one`. These lemmas identify the block inclusions with
  `Fin.cast (blockRanks_add h) (i.castAdd _)` and
  `Fin.cast (blockRanks_add h) (j.natAdd _)`, which are the values of the contiguous
  placement by definition. No other row ordering is chosen.
- `first_succBlockEquiv`, `second_succBlockEquiv`: the first and second blocks of a row
  `z : Fin (t + 1) → R` are `i ↦ z ((succBlockShape m h).index 0 i)` and
  `j ↦ z ((succBlockShape m h).index 1 j)`.
- `join_succBlockEquiv_index_zero`, `join_succBlockEquiv_index_one`: the joined row
  `join (succBlockEquiv h) w v` has value `w i` at `(succBlockShape m h).index 0 i`
  and value `v j` at `(succBlockShape m h).index 1 j`.

So in the positive two-block case the partial Fourier integral
`rowPartialFourierIntegral ψ μ (succBlockEquiv h) f ξ v` transforms exactly the
coordinates of the first block of `succBlockShape m h`.

## Provenance and scope

This is derived internal infrastructure. It makes the source row `(w, v)`, with
`w ∈ F^{t_1}` and `v ∈ F^{t_2}` (printed page 413), agree with the existing Library
block indexing. It reuses the published `blockRanks_add`, `index_zero` and
`index_one`, introduces no analytic content and asserts nothing about
representations.
