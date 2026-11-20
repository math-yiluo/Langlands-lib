# The negative and positive spans and the rank-one translation of the big cell

This internal helper module, used in the proof of
`SplitSimplyConnectedFactorialStatement`, computes the left translate of a
big-cell point by a point `u_a(e₀)` of a simple root group. Throughout, `D` is
a `CellData k G` (module `FactorialCellData`) with base `b`.

## Group theory

- `list_prod_ofFn_split`: in a group, if all factors of a list product
  `f 0 ⋯ f (m-1)` except `f r₀` lie in a subgroup `S`, then the product is
  `A · f r₀ · B` with `A, B ∈ S`.

## Root combinatorics

- `isClosedRootSet_neg` and `isClosedRootSet_pos`: the negative roots and the
  positive roots each form a closed set of roots in the sense of
  `IsClosedRootSet` (closed under sums, no opposite pair).
- `not_isPos_of_root_eq_add`: let `a` be simple and `β` negative with
  `β ≠ -a`. If a root `d` equals `p a + q β` with `p, q ≥ 0` and `q > 0`, then
  `d` is not positive. Writing `β = ∑ g_j α_j` with all `g_j ≤ 0`, some simple
  root `j₀ ≠ a` has `g_{j₀} < 0`; otherwise `β` would be a negative multiple of
  `a`, and reducedness forces `β = -a`. Then `d` has a negative coefficient at
  `j₀`, so all its coefficients are `≤ 0`.
- `root_reflectionPerm_self` and `not_isPos_reflectionPerm_self`: the index
  `s_a(a)` is the root `-a`, which is negative for simple `a`.

## Negative and positive spans

- `negSpan` and `posSpan` are the subgroup functors `rootSpan` (module
  `FactorialCellData`) of the negative and the positive roots;
  `rootPoint_mem_negSpan` and `rootPoint_mem_posSpan` say they contain the
  corresponding root points.
- `conj_rootPoint_mem_negSpan`: for simple `a` and negative `β ≠ -a`,
  `u_a(x) u_β(y) u_a(-x) ∈ negSpan`. By the commutator formula (clause 4 of
  `affineSplitRootSubgroupSpanning`), `u_a(x) u_β(y) u_a(-x) u_β(-y)` is an
  ordered product of points of root groups `p a + q β` with `p, q > 0`, and these
  roots are negative by `not_isPos_of_root_eq_add`.
- `negConj a Z` is the subgroup of points of `negSpan` whose conjugates by all
  `u_a(x)` stay in `negSpan`. It contains `u_β(y)` for negative `β ≠ -a`
  (`rootPoint_mem_negConj`); `conj_mem_negSpan_of_mem_negConj` unfolds the
  definition.

## The rank-one translation

- `rankOneLaws`: for simple `a`, the root groups of `a` and `-a` satisfy the
  rank-one laws `RankOneLaws`
  (`LocalSplitCell.rankOneLaws_of_weylNormalization_affine`, using the
  Weyl normalization in `CellData`). In particular
  `u_a(e₀) u_{-a}(y) = u_{-a}(d⁻¹ y) · a∨(d) · u_a(d⁻¹ e₀)` whenever
  `d = 1 + e₀ y` is a unit.
- `exists_translate_cellPoint`: let `y` be the coordinate of the root `-a` in a
  cell point `cellPoint(c, t, w)`. If `1 + e₀ y = d` is a unit, then
  `u_a(e₀) · cellPoint(c, t, w) = cellPoint(v', a∨(d) t, w')` for some
  coordinates `v'` and `w'`. The proof splits the negative product as
  `A · u_{-a}(y) · B` with `A, B ∈ negConj a`. It applies the rank-one law, moves
  `u_a(d⁻¹ e₀)` past the torus factor (equivariance of the root
  parametrization), and absorbs the conjugated factors into the negative and
  positive spans.

Provenance: internal; an elementary computation with the Library's coordinate
split relations (commutator formula and rank-one laws).
