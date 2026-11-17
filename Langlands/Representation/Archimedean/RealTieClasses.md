# Tie classes of a Langlands-ordered list of real blocks

Module `Langlands.Representation.Archimedean.RealTieClasses`, namespace
`Langlands.Archimedean.RealTieClasses`.

## Purpose and provenance

A Langlands-ordered list `ds` of real blocks (the real parts of the block exponents weakly
decrease, `IsRealLanglandsOrdered`) is cut into its **tie classes**: maximal runs of consecutive
blocks whose exponents have the same real part. This module proves that such a decomposition
exists and derives from it the hypotheses on `ds` used by the limit along the standard parabolic
subgroup `Q` whose diagonal blocks are the classes (`RealLeviLimit`, Worker 5220, Task 6749):

- the position block exponents of `ds` weakly decrease;
- they strictly decrease from one block of `Q` to a later one;
- each twisted class standard module is irreducible, given
  `RealTemperedStandardIrreducibleStatement`.

This is internal infrastructure for the reverse-intertwiner step of Task 7069
(`RealReverseIntertwinerKernelStatement`, module `RealStandardIrreducibleCriterionReduction`).
Worker 5220 plans to import it for the limit-pairing lemmas of Task 6749.

Provenance: derived; elementary combinatorics of lists. No literature statement is claimed. The
grouping by equal real exponent gives the standard parabolic subgroup used in the asymptotics of
matrix coefficients (compare Knapp, *Representation theory of semisimple groups*, 1986, Ch. VIII).

The only result with an external hypothesis is `irreducible_cl` (and `exists_tieData`, which uses
it). Its hypothesis `htemp : RealTemperedStandardIrreducibleStatement` (Library module
`RealTemperedIrreducibleStatement`) is passed as an argument and is not proved here.

## Notation

From `RealLeviSlices` and `RealLeviChartIntegralStatement`, for `dss : Fin c → List RealBlock`:

- `flat dss = dss 0 ++ ⋯ ++ dss (c-1)` (`(List.ofFn dss).flatten`);
- `sz dss i = realRank (dss i)`, the rank of the class `i`, and `N = ∑ i, sz dss i`;
- `start (sz dss) i = sz_0 + ⋯ + sz_{i-1}`, the first position of the block `i` of `Q`;
- `cls (sz dss) p : Fin c`, the block of `Q` containing the position `p : Fin N`;
- `shift dss i = start_i − (N − sz_i)/2` and `cl dss i = twist (shift dss i) (dss i)`, the class
  list twisted by `|det|^{shift dss i}` (each block exponent is shifted by the real number
  `shift dss i`).

From `RealInducedStandardBound`: `realPositionBlockExponent ds p` is the real part of the
exponent of the block of `ds` containing the position `p` (`0` past the end). From the Library:
`realBlockExponent x` is the real part of the exponent of the block `x`.

## Statements

### Position block exponents

- `exists_mem_realPositionBlockExponent ds p hp`: if `p < realRank ds`, there is a block `x ∈ ds`
  with `realPositionBlockExponent ds p = realBlockExponent x`.
- `realPositionBlockExponent_append_left A B p hp`: if `p < realRank A`, then
  `realPositionBlockExponent (A ++ B) p = realPositionBlockExponent A p`.
- `realPositionBlockExponent_append_right A B p`:
  `realPositionBlockExponent (A ++ B) (realRank A + p) = realPositionBlockExponent B p`.
- `realPositionBlockExponent_flat dss i a ha`: if `a < sz dss i`, then
  `realPositionBlockExponent (flat dss) (start (sz dss) i + a) = realPositionBlockExponent (dss i) a`.
- `exists_mem_flat dss p`: for every position `p : Fin N` there is a block `x` in the class
  `dss (cls (sz dss) p)` with `realPositionBlockExponent (flat dss) p = realBlockExponent x`.
- `mem_flat hx`: a block of `dss i` is a block of `flat dss`.

### Tie classes

- `exists_tieClasses ds hord` (**tie classes**): if `ds` is Langlands-ordered, there are `c : ℕ`
  and `dss : Fin c → List RealBlock` with
  1. `flat dss = ds`;
  2. every `dss i` is nonempty;
  3. all blocks of one class `dss i` have the same `realBlockExponent`;
  4. if `i < j`, `x ∈ dss i` and `y ∈ dss j`, then `realBlockExponent y < realBlockExponent x`.

### Conditions along the tie classes

For `dss : Fin c → List RealBlock`:

- `anti_of_tieClasses heq hlt`: under conditions 3 and 4 above, for all positions `p ≤ q` in
  `Fin N`, `realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p`.
- `strict_of_tieClasses hlt`: under condition 4, for all positions `p, q : Fin N` with
  `cls (sz dss) p < cls (sz dss) q`,
  `realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p`.
- `irreducible_cl htemp heq i`: given `RealTemperedStandardIrreducibleStatement` and condition 3,
  the `(𝔤𝔩_{sz_i}(ℝ), O(sz_i))`-module of `O(sz_i)`-finite functions of
  `realStandardModule (sz dss i) (cl dss i)` is irreducible (`IsIrreducibleGKModule` for
  `realStandardRep`, `realStandardLie`).

### Tie data

- `exists_tieData htemp ds hord`: given `RealTemperedStandardIrreducibleStatement` and a
  Langlands-ordered list `ds`, there are `c` and `dss : Fin c → List RealBlock` with
  `flat dss = ds`, the weak decrease of `anti_of_tieClasses`, the strict decrease across blocks of
  `strict_of_tieClasses`, and irreducibility of every twisted class standard module as in
  `irreducible_cl`.

## Proofs

- Position lemmas: induction on the list, following the defining equations of
  `realPositionBlockExponent` (a character block takes one position, an induction block two).
  `realPositionBlockExponent_flat` is by induction on `c` with `flat_succ`,
  `start_zero'` and `start_succ'`, using the append lemmas. `exists_mem_flat` writes `p` as
  `start (sz dss) (cls p) + a` with `a < sz_{cls p}` (`pos_cls`, `val_pos`) and applies the
  previous two lemmas.
- `exists_tieClasses`: induction on `ds`. The empty list has `c = 0`. For `b :: ds`, take the
  classes of `ds`. If there are none, `ds = []` and the classes are `[[b]]`. Otherwise, if every
  block of the first class has the exponent of `b`, put `b` at the front of the first class
  (`Fin.cons (b :: dss 0) (fun i => dss i.succ)`). If not, some block `x1` of the first class has
  `realBlockExponent x1 ≠ realBlockExponent b`; Langlands order gives `≤`, so it is `<`, and the
  first class has constant exponent, so `[b]` becomes a new first class (`Fin.cons [b] dss`). The
  four conditions are checked by `Fin.cases` on the class indices.
- `anti_of_tieClasses`, `strict_of_tieClasses`: by `exists_mem_flat`, each position exponent is
  the exponent of a block in the class of that position. `p ≤ q` gives `cls p ≤ cls q`
  (`cls_mono`); in the case `<` use condition 4, in the case `=` condition 3.
- `irreducible_cl`: `realRank (cl dss i) = sz dss i` (`realRank_cl`). Every block of `cl dss i` is
  `twistBlock (shift dss i) x'` with `x' ∈ dss i`, and
  `realBlockExponent (twistBlock s x') = realBlockExponent x' + s`
  (`realBlockExponent_twistBlock`). So the real exponent is constant on `cl dss i` by condition
  3, and `htemp` applies.
- `exists_tieData`: combine the four previous results.
