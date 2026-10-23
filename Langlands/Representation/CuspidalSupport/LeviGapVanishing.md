# Deep vanishing of averaged torus translates on a product Levi

Authors: Worker 237.

Auxiliary module for the admissibility proof
`Langlands/Representation/CuspidalSupport/QuasicuspidalLeviAdmissibilityProof.lean`.
It uses neither the Cartan decomposition nor Schur's lemma, so other proofs can
import it on its own. All declarations are in the namespace
`Langlands.CuspidalSupport.LeviAdmissibility`.

Throughout, `K` is a nonarchimedean local field (`IsNonarchimedeanLocalField`,
with its `ValuativeRel` and topology), `v = ValuativeRel.valuation K`, and `B` is a
block shape, so `B.Levi K` is the product of the groups `GL_{B.size j}(K)`.
`leviTorus B ϖ λ` (from `LeviSplitContraction`) is the block-diagonal torus
element with entries `ϖ^{λ j b}`.

## Source

This module carries out the step of Bernstein and Zelevinsky 1976 (literature id
`bernstein-zelevinsky-1976-representations-gln`) behind the compact support of
matrix coefficients in Harish-Chandra's Theorem 3.21 and Lemma 3.22. In the source,
the Jacquet module of a quasicuspidal representation vanishes, so translates by
torus elements far inside a chamber average to zero. Here this is stated directly
for averages over compact open subgroups, in the form the admissibility proof needs.
It is internal, derived material: no statement here is quoted from the source.

## Compact open integral subgroups

- `isOpen_integralRange` and `isCompact_integralRange`: for every rank `m`, the
  integral subgroup `Iwasawa.integralRange v m` of `GL_m(K)` is open and compact.
  For `m = 0` the group is trivial. For `m + 1` it equals the published level-zero
  subgroup `Conductor.levelOpenSubgroup K m 0` (via `Iwasawa.integralRange_succ`
  and `Conductor.levelSubgroup_zero`), which is open and compact
  (`Conductor.isCompact_levelOpenSubgroup`).
- `integralLevi B` is the open subgroup of `B.Levi K` given by the product of the
  integral subgroups of the blocks. `mem_integralLevi` characterizes membership
  blockwise, and `isCompact_integralLevi` follows from Tychonoff's theorem for the
  finite product.

## Deep vanishing

- `exists_gap_average_eq_zero`: let `ρ` be a smooth complex representation of
  `B.Levi K` with `IsLeviQuasicuspidal B ρ`, `ϖ` a uniformizing element, `H` a
  compact open subgroup, `c ∈ B.Levi K`, `w ∈ V`, `i` a block and `a + 1 < B.size i`.
  Then there is `N : ℤ` such that the `H`-average `Compact.averageMap ρ hρ H hH` of
  `ρ(c · leviTorus B ϖ λ) w` is zero for every blockwise antitone `λ` with
  `N ≤ λ_i(a) - λ_i(a+1)`.

  Proof. The refined parabolic `splitRefinement B i a ha` is proper
  (`splitRefinement_parabolic_ne_top`). Quasicuspidality makes its Jacquet
  coinvariants trivial, so `w` lies in the coinvariant kernel. That kernel is the
  span of the vectors `ρ(u) y - y` with `u` in the refined unipotent radical. The
  claim is linear in `w` (for sums, take the larger bound), so it suffices to treat
  one generator. For such `u` and `t = leviTorus B ϖ λ`,
  `c t u = (c (t u t⁻¹) c⁻¹) · c t`. The set of block-`i` elements `g` with
  `c · Pi.mulSingle i g · c⁻¹ ∈ H` is an open neighbourhood of `1`. Since `u` is
  `1` outside block `i` (`mem_splitRefinement_unipotent`, `leviTorus_conj_of_eq_one`),
  `torus_conj_eventually_mem` puts `c (t u t⁻¹) c⁻¹` in `H` once the gap is at
  least `N`. Averaging over `H` is invariant under translation by elements of `H`
  (`Compact.orbitMean_apply`), so the averages of `ρ(c t)(ρ(u) y)` and `ρ(c t) y`
  agree.
- `exists_uniform_gap_bound`: one bound `N` serves finitely many pairs
  `(c x, w x)` and all blocks and split points at once. It is the maximum of the
  bounds above over a finite index set.

## Bounded gaps

- `BoundedGapReps B N` says that there is a finite set `Λ₀` of exponent tuples
  such that every blockwise antitone `λ` whose consecutive gaps are all below `N`
  equals some `μ ∈ Λ₀` plus a constant `c j` in each block `j`.
- `sub_last_le`: if every gap of `f : Fin m → ℤ` is below `N`, an entry `k` steps
  before the last one exceeds the last one by at most `k · |N|` (induction on `k`).
- `boundedGapReps` proves `BoundedGapReps B N` for every `N`. Take `c j` to be the
  last exponent of block `j`. Then `0 ≤ λ_j(b) - c j` by antitonicity, and
  `λ_j(b) - c j ≤ (B.size j) · |N|` by `sub_last_le`. So `μ = λ - c` lies in a finite
  box.
