# The source side of the separated discrete-series case

Lean module: `Langlands.Representation.Archimedean.RealDiscreteSeparatedSource`, part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteSeparated`.

## Purpose and provenance

The module proves no statement of record. It fixes the principal series that presents the
standard module in the separated case, chooses the row sets of the minors, and shows that this
principal series is the twist of an even principal series by the product of the minors. All
declarations are internal.

Data. `cs : List RealCharacterData` (in the application the even characters come first) and
`Ds = [D₁, …, D_d] : List ComplexCharacterData`, sorted by decreasing absolute weight. For
`D` of weight `m` and exponent `t`, `ℓ = |m|`:

* `xChar D = cb D 0 = |·|^{t − ℓ/2}`, `yChar D = ca D (ySign D) = sgn^{ℓ+1} |·|^{t + ℓ/2}`
  (Library characters of `RealInducedCharacterMaps`; `ySign` from `RealDiscretePresentation`);
* `srcChars cs Ds = x(D₁), …, x(D_d), cs, y(D_d), …, y(D₁)`, a list of length
  `n = 2d + |cs|`. Positions `< d` are the `x`-rows, positions `d … d + |cs| − 1` the character
  rows, and position `d + |cs| + P` is the `y`-row of the `P`-th block of `Ds.reverse`.

## Declarations

* `realPositionExponent_map_character`: the `i`-th exponent of a character list is the exponent
  of its `i`-th character.
* `sourceList_eq`, `srcChars_length`, `srcChars_x`, `srcChars_c`, `srcChars_y`: `srcChars` is the
  `sourceList` of `RealDiscretePresentation` with `M = cs`, and its entries by position.
* `kOf Ds P = |m_P| + 1` for the `P`-th block of `Ds.reverse` (`0` past the end) and
  `oddAt cs x` (the `x`-th character of `cs` is odd), with `kOf_eq`, `oddAt_iff`,
  `parity_val_of_not_oddAt`, `kOf_pos`, `kOf_le` (`kOf ≤ N` when `|m| + 1 ≤ N` for all
  blocks), and the monotonicity lemmas `kOf_mono` (`Ds.reverse` has increasing absolute
  weights) and `oddAt_mono` (odd characters come last).
* `rowSet cs Ds n N j` (`j < N`): the `y`-rows of the blocks `P` with `j < k_P`, and for `j = 0`
  also the rows of the odd characters. `hitCount cs Ds i` is `k_P` on the `y`-row of `P`, `1`
  on an odd character row, and `0` otherwise.
* `isBottom_rowSet`: each `rowSet j` is a bottom segment of `Fin n`. Proof: the `y`-rows with
  `j < k_P` form a final segment because `k_P` increases with `P`; for `j = 0` all `y`-rows are
  included (`k_P ≥ 1`) and the odd character rows are the last character rows.
* `colSet_rowSet`, `hits_rowSet`: the rows `j` with `i ∈ rowSet j` form the initial segment
  `seg N (hitCount i)`; so `hits (rowSet) i = hitCount i` (needs `|m| + 1 ≤ N` and `1 ≤ N`).
* `rowSet_parity`: the sign of the `i`-th character of `srcChars` is `(−1)^{hitCount i}`:
  `x`-rows are even, a character `sgn^ε |·|^t` has sign `(−1)^ε`, and `y(D)` has sign
  `(−1)^{ℓ+1} = (−1)^{k_P}`.
* `isMinorShift_src` (**the source is a shift**): for sorted data and `N` with
  `|m| + 1 ≤ N` and `1 ≤ N`,
  `IsMinorShift n ((shiftList n src (rowSet)).map character) src (rowSet)`, where
  `src = (srcChars cs Ds).map character`. This is `isMinorShift_shiftList` (module
  `RealDiscreteShiftSort`) with `isBottom_rowSet` and `rowSet_parity`.
* `midList cs Ds`: the even characters `|·|^{t − ℓ/2}` (`x`-rows), `|·|^{t − ε}` (for each
  character `sgn^ε |·|^t` of `cs`) and `|·|^{t + ℓ/2 − (ℓ + 1)}` (`y`-rows, in the order of
  `Ds.reverse`). `midList_length`, `midList_x`, `midList_c`, `midList_y`.
* `shiftList_eq_midList`: the shifted list of `isMinorShift_src` is `midList cs Ds`; each
  exponent is lowered by `hitCount i` (`0` on `x`-rows, `ε` on character rows, `ℓ + 1` on
  `y`-rows).
