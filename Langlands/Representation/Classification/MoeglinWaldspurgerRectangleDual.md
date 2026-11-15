# The MW algorithm on integer rectangles

Worker 38. This module computes the Library's integer-line
Moeglin–Waldspurger algorithm (`Langlands.MoeglinWaldspurger.dual`, module
`MoeglinWaldspurger`) on rectangles. It then identifies the realization of a
rectangle with Tadić's centered multisegment `a(r,d)^ρ`
(`Classification.tadicMultisegment`). This is the combinatorial content of
Badulescu, *On p-adic Speh representations* (2014), Theorem 1(a)
(retained `1110.5080.tex`, line 149: `i(u(δ,k)) = u(τ,l)` for `δ = Z(ρ,l)`,
`τ = Z(ρ,k)`). The proof there, at line 157, reads only "obvious by MWA". The
module proves the integer-line computation. It does not assert any
representation-theoretic duality: identifying the computed dual with the
actual Aubert dual uses the separately proved proposition
`MoeglinWaldspurger.AubertCorrectness`, whose published proof is applied by
`SpehNeighborProductIrreducibilityProof`.

## Definitions

- `rectangleRow b m i` is the integer interval `[b+i, b+i+m]`, which has
  `m+1` points.
- `rectangle b n m` is the multiset of the `n+1` rows `rectangleRow b m i`,
  `0 ≤ i ≤ n`. So it has `n+1` rows of `m+1` points each, and consecutive rows
  are shifted by one.

## Main results

- `dual_rectangle b n m : dual (rectangle b n m) = rectangle b m n`. The MW
  dual of a rectangle is its transpose, with the same base point `b`.
- `realize_rectangle ρ b n m x hx`: if `x + b = -(n+m)/2`, then
  `realize ρ x (rectangle b n m) = tadicMultisegment ρ (n+1) (m+1) _`. The
  realized rectangle is the centered `a(n+1, m+1)^ρ`. The hypothesis on `x`
  is exactly the centering condition. The cuspidal datum `ρ` is arbitrary
  (not necessarily unitary), and the universes are those of the Library's
  realization map.

## Proof

The helper lemmas follow one MW round on a rectangle.

- `rectangleRow_le_of_le` and `sort_rows`: in the Library's descending order
  (ending first, then beginning), the rows are sorted from the top row
  `i = n` down to `i = 0`.
- `pick_rows`: among rows `0, …, j`, the only row that ends at `b+j+m` and
  begins strictly below `b+j+1` is row `j`.
- `chain_rows`: by induction on `j`, the chain below the top row selects every
  remaining row in descending order and leaves no untouched occurrence.
- `round_rectangle`: one round on `rectangle b n m` selects all `n+1` rows.
- `selected_rectangle` and `emitted_rectangle`: the selected occurrences are
  the whole rectangle. The emitted interval is `[b+m, b+m+n]`, which is the
  last row of the transposed rectangle.
- `dropLast_rectangleRow_succ` and `dropLast_rectangleRow_zero`: right
  truncation shortens each row by one point. One-point rows vanish.

`dual_rectangle` is proved by induction on `m`, using the Library's recursive
equation `dual_of_round`. When `m = 0`, the residual is empty and the output
is the single emitted interval, i.e. `rectangle b 0 n`. In the inductive step,
the residual is `rectangle b n m`. The induction hypothesis transposes it to
`rectangle b m n`. Adding the emitted row `[b+m+1, b+m+1+n]` gives
`rectangle b (m+1) n`.

`realize_rectangle` compares the two multisets termwise along
`Multiset.range (n+1)`, using segment extensionality (`Segment.ext_base_length`).
Row `i` realizes to base `ρ` twisted by `x+b+i` and length `m+1`. Tadić's
`j`-th segment has base `ρ` twisted by `j-n/2-m/2` and length `m+1`. The bases
agree by the centering hypothesis.

## Provenance

The rectangle computation is a derived internal lemma. It does not depend on
any unproved target. The Library's algorithm follows Moeglin–Waldspurger,
*Sur l'involution de Zelevinski* (1986), II.1–II.2, in Badulescu's
shortest-segment form (`1110.5080.tex`, lines 107–134).
