# A tightness criterion for families of column sets

Lean module: `Langlands.Representation.Archimedean.RealDiscreteTightness`, part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteTightness`. The module imports only Mathlib.

## Purpose and provenance

The module proves no statement of record. It is a combinatorial lemma used in the scalar step
for discrete-series blocks (module `RealDiscreteSeparatedRelations`): a family of column sets
whose frame vector survives the rotation conditions is forced to be one specific family. The
lemma and its proof are internal.

## Notation

* `D : Fin N → Finset (Fin n)`: a family of `N` sets of columns ("rows" `j < N`).
* `colSet D x = {j | x ∈ D j}`: the rows whose set contains the column `x`.
* `seg N c = {j : Fin N | j < c}`: an initial segment.

## Declarations

* `mem_colSet`, `mem_seg`: membership.
* `sum_card_eq`: `Σ_j |D j| = Σ_x |colSet D x|` (both count the incidences `x ∈ D j`).
* `sum_weight_eq`: `Σ_j j · |D j| = Σ_x Σ_{j ∈ colSet D x} j` (the incidences weighted by `j`).
* `map_seg`, `card_seg`, `sum_seg`: for `c ≤ N`, `seg N c` corresponds to `range c`, has `c`
  elements and weight sum `0 + 1 + … + (c − 1)`.
* `val_le_of_strictMono`, `sum_orderEmbOfFin`, `sum_range_le_sum`: listing a set `E ⊆ Fin N` in
  increasing order, its `i`-th element is at least `i`; hence
  `Σ_{j ∈ E} j ≥ 0 + 1 + … + (|E| − 1)`.
* `eq_seg_of_sum`: equality holds only when `E = seg N |E|`. If some element is strictly larger
  than its index, the sum is strictly larger; so the `i`-th element of `E` is `i` for every `i`.
* `eq_of_tight` (**tightness**). Hypotheses: `|D j| = |D' j|` for every `j`; for every column
  `x` there is `c_x ≤ min(N, |colSet D x|)` with `colSet D' x = seg N c_x`. Conclusion:
  `D = D'`.

  Proof. By `sum_card_eq` and the first hypothesis, `Σ_x c_x = Σ_x |colSet D x|`; with
  `c_x ≤ |colSet D x|` this gives `|colSet D x| = c_x` for every `x`. By `sum_weight_eq`, the
  weight sums satisfy `Σ_x Σ_{seg c_x} j = Σ_x Σ_{colSet D x} j`, and termwise
  `Σ_{seg c_x} j ≤ Σ_{colSet D x} j` by `sum_range_le_sum`. So every term is an equality, and
  `eq_seg_of_sum` gives `colSet D x = seg N c_x = colSet D' x` for all `x`. Hence `D = D'`.
