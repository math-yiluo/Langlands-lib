# Compact open normal refinement for VIII.1.3

This module constructs the topological refinement used in Waldspurger VIII.1.3
and elementary adapters for returning from the refined level to the original
compact open subgroup. It does not assert an induced-model comparison or
spectral finiteness.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d’après Harish-Chandra)* (2003), printed p. 321, the paragraph following
Remarque VIII.1.3(i),(ii). Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source refines the compact open level inside the chosen special maximal
compact subgroup, normal in that compact subgroup. Only openness and
compactness of the latter are used for this topological step, so the generic
construction is stated for any compact open `K` in any topological group.

The rational-point specialization retains the canonical topology, arbitrary
nonarchimedean local fields and affine locally finite type group schemes. It
needs neither splitness nor characteristic zero, and makes no restriction on
relative rank. The nonzero-fixed-vector adapter allows a carrier universe
independent of the group universe.

## Declarations and dependency ledger

All names below have namespace `Langlands.HarishChandraSchwartz`.

| Declaration | Content and dependencies | Status |
| --- | --- | --- |
| `CompactOpenNormalRefinementStatement K` | Every subgroup `H` with explicit openness and compactness has a compact open refinement `L ≤ H`, `L ≤ K`, with `(L.subgroupOf K).Normal`. | Prop-valued target. |
| `compactOpenNormalRefinement K hKc` | Constructs the exact refinement using compactness of `K`. | Closed topological adapter from Mathlib. |
| `finite_of_compactOpenNormalRefinement` | An antitone set family finite at every contained normal compact open level is finite at every compact open level, assuming the displayed refinement proposition. | Conditional elementary finiteness adapter. |
| `fixedVectors_ne_bot_of_le` | A nonzero `H`-fixed vector remains fixed on `L ≤ H`. | Closed elementary fixed-vector adapter using `Langlands.fixedVectors_antitone`. |
| `RationalCompactOpenNormalRefinementStatement G` | The exact target for every compact open `K` on the actual canonical rational-point group. | Prop-valued specialization. |
| `rationalCompactOpenNormalRefinement G` | The canonical rational-point group satisfies that target. | Closed specialization of the generic topological construction. |

Normality is a conclusion concerning the subgroup inside `K`, rather than
ambient normality in `G`, and no refinement witness is stored in structural
data. The rational target does not require an existing special-maximal-compact
choice: callers use their chosen special maximal compact as `K`, with its
explicit openness and compactness proofs. The finiteness adapter does not
provide any finite-index or analytic premise by itself.

## Implemented proof

Inside the compact topological group `K`, the pullback of `H` is an open
subgroup and hence clopen. Apply Mathlib's
`IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`
(`Mathlib.Topology.Algebra.ClopenNhdofOne`) to obtain an open normal subgroup
`N` of `K` contained in that pullback. Its image under the subgroup inclusion
is open in the ambient group because `K` is open, and compact because `N` is
closed in the compact group `K`. Injectivity of the inclusion identifies its
pullback with `N`, proving normality in `K`. The hypothesis that `H` is compact
is retained in the public target although this construction only uses its
openness.

For the set-family adapter, choose this `L` and use antitonicity to include the
set at `H` in the finite set at `L`. For fixed vectors, antitonicity of the
fixed-vector submodule implies that vanishing at `L` would force vanishing at
`H`. The rational specialization installs the canonical rational-point topology
and `Langlands.Plancherel.rationalPoints_nonarchimedeanGroup`.

The actual literal-Levi intersection level, its compactness, the induced-fixed
comparison at normal levels, all/proper VIII.1.2 inputs, and Fourier support
are separate declarations. Nothing here proves those analytic comparisons.
