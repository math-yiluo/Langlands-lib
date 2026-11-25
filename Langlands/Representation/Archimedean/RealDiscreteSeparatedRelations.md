# Relations between the frame vectors of the separated discrete-series case

Lean module: `Langlands.Representation.Archimedean.RealDiscreteSeparatedRelations`, part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteSeparated`.

## Purpose and provenance

The module proves no statement of record. It verifies the hypothesis `hrel` of the scalar step
`hasScalarCommutant_of_frame` (module `RealDiscreteFrame`) for the target list of the
separated case, the frame `frameU n |cs|` (module `RealDiscreteComplexFrame`) and the row sets
`rowSet` (module `RealDiscreteSeparatedSource`). All declarations are internal. The argument is
the frame-vector form of the statement that the minimal `O(n)`-type occurs once: a frame vector
whose image could have a nonzero value at `1` is forced, by rotation weights, sign parities and
tightness (`RealDiscreteTightness`), to be one of the families `tgtSet S`, and plane flips
relate all of these to `tgtSet ∅`.

## Notation

* `tgtList cs Ds = cs.map character ++ Ds.reverse.map induced`. With `a = |cs|`, the columns
  `l < a` are the character columns, and the block `P` of `Ds.reverse` (block `D_{d−P}`) has the
  `z`-column `a + 2P` and the `z̄`-column `a + 2P + 1`.
* `kOf Ds P = |m_P| + 1`, `oddAt`, `rowSet` as in `RealDiscreteSeparatedSource`.
* `u_D = frameVec hsh T (frameU n a) D` for a family `D : Fin N → Finset (Fin n)`;
  `ev`, `IsKEquivariant` as in `RealDiscreteScalarFunctional`.

## Declarations

* `realRank_map_induced`, `realRank_tgtList` (`realRank (tgtList cs Ds) = |cs| + 2|Ds|`),
  `realInducedBlockAt_map_character_append`, `realInducedBlockAt_map_induced`,
  `realInducedBlockAt_tgtList` (the block at position `a + 2P` is `Ds.reverse[P]`),
  `realPositionCharacter_map_character_append` (the character at a character column `l < a` is
  that of `cs[l]`).
* Target families. For a set `S` of planes, `memb cs Ds S j x` says: for a character column
  `x`, `x` is odd and `j = 0`; for a plane column of plane `P`, `j < k_P` and the column is the
  `z̄`-column exactly when `P ∈ S`. `tgtSet cs Ds n N S j = {x | memb S j x}` and
  `cnt S x` is the number of `j` with `memb S j x` (`memb_iff_lt_cnt`, `colSet_tgtSet`:
  the column sets of `tgtSet S` are initial segments `seg N (cnt S x)`; `cnt_le`). The lemmas
  `memb_char`, `memb_plane`, `memb_z`, `memb_zbar`, `mem_tgtSet`, `mem_rowSet` unfold the
  definitions.
* `rowCol`, `colRow`, `rowCol_lt`, `colRow_lt`, `card_tgtSet`: the map sending the `y`-row of
  plane `P` to its `z`- or `z̄`-column (according to `S`) and a character row to its column is a
  bijection from `rowSet j` onto `tgtSet S j`; so `|tgtSet S j| = |rowSet j|`.
* `colCount D x = |colSet D x|` (`colCount_val`) and `domSet D`: the planes whose `z̄`-column is
  hit more often than their `z`-column.
* `eq_tgtSet_of_tight` (**tight families are target families**): if `|D j| = |rowSet j|` for all
  `j`, every odd character column is hit at least once, and for every plane one column is hit at
  least `k_P` times more often than the other, then `D = tgtSet (domSet D)`. Proof:
  `eq_of_tight` (module `RealDiscreteTightness`) with `D' = tgtSet (domSet D)`, using
  `card_tgtSet`, `colSet_tgtSet` and, column by column, `cnt (domSet D) x ≤ |colSet D x|`.
* `sum_sum_eq_sum_card`, `sum_rotC`: the rotation weight of `D` for the plane `(p, p + 1)` is
  `Σ_j Σ_{l ∈ D_j} rotC(p, l) = |colSet D (p+1)| − |colSet D p|`.
* `kmat_flip`, `prod_prod_flip`: the matrix of the sign matrix
  `RealTiedMinorScalar.flip q` (Library) is `diag(−1 at q)`, and
  `∏_j ∏_{x ∈ D_j} (−1 if x = l) = (−1)^{|colSet D l|}`.
* `frameVec_eq_zero`: if `|D j| ≠ |R j|` for some `j`, then `u_D = 0` (all its minors vanish).
* `ev_eq_zero_of_plane` (**rotation vanishing at a plane**): if
  `| |colSet D (a+2P+1)| − |colSet D (a+2P)| | ≤ |m_P|`, then `ev (L u_D) = 0` for every
  equivariant `L`. Proof: `kmat_rot_mul_frameU`, `sum_rotC`, `realInducedBlockAt_tgtList` and
  `ev_frameVec_eq_zero_of_rotation`.
* `ev_eq_zero_of_parity` (**parity vanishing**): if a character column `l` is hit a number of
  times whose parity differs from the parity of `cs[l]`, then `ev (L u_D) = 0`. Proof: the sign
  matrix `flip l` commutes with the frame (`diagonal_mul_frameU`), so `ev_frameVec_sign` gives
  `(−1)^{|colSet D l|} ev (L u_D) = (−1)^{parity(cs[l])} ev (L u_D)`.
* `tgtSet_insert`, `not_mem_both` (**plane flips**): for `P ∉ S`, swapping the two columns of
  plane `P` maps `tgtSet S j` to `tgtSet (insert P S) j`, and no `tgtSet S j` contains both
  columns of a plane.
* `exists_chain`: for every `S ⊆ range |Ds|` there is `c` with
  `ev (L u_{tgtSet S}) = c · ev (L u_{tgtSet ∅})` for all equivariant `L`. Induction on `S`
  (`Finset.induction_on`): the sign matrix `flip q` at the `z̄`-column `q` of `P` maps `U` to `U`
  with the columns of `P` exchanged (`diagonal_flip_mul_frameU`); with `minor_submatrix_swap`,
  `not_mem_both` and `tgtSet_insert`, `ev_frameVec_flip` gives
  `ev (L u_{tgtSet (insert P S)}) = χ(a) · ev (L u_{tgtSet S})`.
* `exists_frame_rel` (**the relations**). Let `n = 2|Ds| + |cs|`, `|m| + 1 ≤ N` for all blocks,
  `1 ≤ N`, `IsMinorShift n ps qs (rowSet cs Ds n N)`, and `T` fixed by `O(n)`. For every family
  `D` there is `c` with `ev (L u_D) = c · ev (L u_{tgtSet ∅})` for every equivariant
  `L : KF n qs → KF n (tgtList cs Ds)`. Proof by cases: if some `|D j| ≠ |rowSet j|`, then
  `u_D = 0` and `c = 0`; if some plane has rotation weight at most `|m_P|` in absolute value,
  or some character column has the wrong parity, then `c = 0` by the vanishing lemmas.
  Otherwise every plane has weight at least `|m_P| + 1 = k_P` in absolute value and every odd
  character column is hit an odd number of times. Then `D = tgtSet (domSet D)` by
  `eq_tgtSet_of_tight`, and `exists_chain` gives `c`.
