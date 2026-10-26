# Polygon comparison for dominance-maximal cones

Author: Worker 23.

This module is the numerical core of the proof of
`Langlands.GLMaximalConeJacquetQuotientStatement` (task b291a31b). It compares
two piecewise-linear prefix polygons in standard GL coordinates. The first is
the polygon of a cone of a finer block vector. The second is the polygon of a
coarse positive part with the same block totals. If no cone strictly dominates
the coarse polygon, in the sense of the published
`Langlands.GLBlockPositivePartStrictlyDominates`
(`Langlands.Representation.Classification.MaximalConeStatement`), then every
partial residual inside a coarse block is nonpositive. This is the
exponent-bound step in Konno 2003, Lemmas 3.3–3.4 (dominance maximality forces
the twisted Jacquet quotient into the tempered chamber). The Lean statements
are elementary inequalities about finite sums. They are internal helpers, not
transcriptions of a numbered source result.

## Generic regrouping

In namespace `Langlands.MaximalConePolygon`:

- `sum_filter_comp q Q f`: a sum over `{k | Q (q k)}` regroups as a sum over
  `j` with `Q j` of the sums over the fibres `q k = j`.
- `sum_filter_le_split q hq f i₀`: for monotone `q`, the sum over `k ≤ i₀`
  splits into the sum over `q k < q i₀` plus the sum over `q k = q i₀ ∧ k ≤ i₀`.
- `pre v m`: the sum of `v x` over the coordinates `x : Fin n` with `x < m`.
  `pre_split` splits it at `u ≤ w`. `pre_sub` subtracts two vectors.
  `pre_of_le` says `pre v m = pre v n` for `m ≥ n`.
- `pre_nonneg_of_antitone d ...`: if `d` is antitone on the coordinates in
  `[a, b)` and `pre d a ≥ 0` and `pre d b ≥ 0`, then `pre d m ≥ 0` for
  `a ≤ m ≤ b`. If some `pre d m` were negative, some `d x₀` with
  `a ≤ x₀ < m` would be negative. Then every later increment up to `b` would be
  negative as well, contradicting `pre d b ≥ 0`.

## Block positions

In namespace `Langlands.GeneralLinear.BlockShape`:

- `B.startN m`: the sum of the sizes of the blocks numbered below `m`, i.e. the
  first ambient coordinate after them.
- The existing `Langlands.Geometric.blockIndex B x = (B.indexEquiv.symm x).1`
  gives the block containing the ambient coordinate `x`. This is exactly the
  expression used in `GLBlockPositivePartStrictlyDominates`; the positive part
  is `fun x => t (Geometric.blockIndex C x)`.
- `indexEquiv_val`: `B.indexEquiv ⟨i, a⟩ = B.startN i + a`.
- `blockIndex_spec`, `lt_startN_iff`
  (`x < B.startN m ↔ Geometric.blockIndex B x < m`), `blockIndex_eq_iff`,
  `startN_mono`, `startN_succ`, `startN_of_length_le`, `startN_le`.
  Monotonicity reuses the published `Geometric.blockIndex_monotone`.
- `sum_blockIndex g P`: summing `g (Geometric.blockIndex B x)` over coordinates in the blocks
  satisfying `P` gives `∑_{P k} B.size k * g k`.
- `startN_coarsen hsize j`: the size identity alone gives
  `C.startN j = ∑_{q i < j} B.size i`. For monotone `q`, the published
  `Langlands.blockIndex_coarsening B C q hq hsize x` gives
  `Geometric.blockIndex C x = q (Geometric.blockIndex B x)`.

## Cones

- `fibre_residual_eq_zero hsize htot j`: if `C.size j = ∑_{q k = j} B.size k`
  and `∑_{q k = j} r k = C.size j * t j`, then the residuals
  `r k - B.size k * t (q k)` sum to zero over each fibre. `sum_filter_comp_eq_zero`
  extends this to unions of fibres.
- `IsCone B r C q t`: the six cone conditions of the target statement, verbatim:
  `q` monotone and surjective, the size identity, `t` strictly antitone, block
  totals `∑_{q i = j} r i = C.size j * t j`, and nonpositive partial residuals
  `∑_{q k = q i, k ≤ i} (r k - B.size k * t (q i)) ≤ 0`.
  The existing `GLBlockConeNumericalConditions B C r q t` packages these
  propositions as a conjunction; this structure retains its named
  fields, since the two definitions are not identical.
- `IsCone.sum_le_of_le hc i` and `IsCone.sum_le_of_downClosed hc s hs`: for a
  cone, the residuals sum to at most zero over every initial segment `k ≤ i`.
  The same holds over every down-closed set of blocks, which is an initial
  segment. Split the segment by `sum_filter_le_split`: whole earlier fibres
  contribute zero, and the partial fibre is the cone condition.
- `pre_blockIndex_eq`: the prefix sum of a block function up to a coordinate
  boundary given by a block predicate, as a weighted block sum.

## The comparison

Fix a block vector `r` along `B`, a coarse positive part `(C, p, t)` with
monotone `p`, the size identity and the block totals of `r` (hypotheses `hp`,
`hpsize`, `hptot`; no antitonicity of `t` is needed), and any cone
`hc : IsCone B r C'' q'' t''`. Write `L(m) = pre (t ∘ (Geometric.blockIndex C)) m` and
`L''(m) = pre (t'' ∘ (Geometric.blockIndex C'')) m`.

- `knot_le` (private): `L(C.startN m) ≤ L''(C.startN m)`. By `blockIndex_coarsening`
  both polygons are block functions along `B`. The `B`-blocks below
  `C.startN m` form a down-closed set. On it, the cone bound gives
  `∑ r ≤ ∑ B.size * t'' ∘ q''`, while the coarse totals give
  `∑ r = ∑ B.size * t ∘ p`.
- `pre_le_of_cone`: `L(m) ≤ L''(m)` for every `m`. The difference
  `d = t'' ∘ (Geometric.blockIndex C'') - t ∘ (Geometric.blockIndex C)` is antitone inside each `C`-block,
  because `t ∘ (Geometric.blockIndex C)` is constant there and `t''` is strictly antitone. The
  knots `C.startN j` give nonnegative values, so `pre_nonneg_of_antitone` applies
  on each `C`-block. Past the last block, `pre_of_le` reduces to the final knot.
- `pre_total_eq_of_cone`: `L(n) = L''(n)`, since both totals equal `∑ r`.
- `pre_lt_of_cone hp hpsize hptot hc i hi`: if
  `0 < ∑_{p k = p i, k ≤ i} (r k - B.size k * t (p i))`, then
  `L(B.startN (i+1)) < L''(B.startN (i+1))`. The cone bound on `k ≤ i` gives
  `∑_{k ≤ i} r k ≤ ∑_{k ≤ i} B.size k * t'' (q'' k)`. By the hypothesis and the
  zero sums over earlier `p`-fibres, `∑_{k ≤ i} B.size k * t (p k)` is strictly
  smaller than `∑_{k ≤ i} r k`.
- `strictlyDominates_of_cone`: under the same hypothesis,
  `GLBlockPositivePartStrictlyDominates C'' t'' C t`. The totals agree, every
  prefix inequality is `pre_le_of_cone`, and the strict one is at
  `B.startN (i+1) ≤ n`.
- `residual_nonpos_of_not_strictlyDominates`: the contrapositive. If the cone
  `(C'', q'', t'')` of `r` does not strictly dominate `(C, t)`, every partial
  residual of `r` inside a `p`-fibre is nonpositive.

In the proof of the target, `r` is the real part of a lifted exponent along a
refinement of the selected cone `C`. The maximality clause rules out strict
dominance by any cone of `r`, and a cone exists by the cone-existence
proposition `GLBlockConeExistenceStatement`, a hypothesis of the assembly
theorem (module `MaximalConeAssembly`).

## Sources

T. Konno, *A note on the Langlands classification and irreducibility of induced
representations of p-adic groups* (2003), registered as
`konno-2003-langlands-classification`: the order on p.394, Lemmas 3.3–3.4
(pp.394–396) and Theorem 3.5(i) (pp.396–397) give dominance of positive parts
and the maximal choice. This module proves only the elementary polygon
inequalities used in that argument.
