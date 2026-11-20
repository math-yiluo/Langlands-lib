# Pullbacks are locally covered by charts inside pair-chart patches

Module `Langlands.Geometry.Analytic.PairChartCover`, namespace
`Langlands.Analytic.SaturatedAtlasPresentation`.

## Purpose and provenance

This is an internal prerequisite for Task 7765
(`CompactPullbackActionContinuityStatement`). No literature statement is
transcribed. Take a commutative square `p ≫ f = q ≫ g` in the localized
analytic category. The theorem shows that every point of `P` is locally
covered by finitely many charts of `P`, each lying inside the patch
`c.patch p q` of some pair chart `c : PairChartData f g`
(`PairChartPatch`). Consequently, any chart property that holds for all
charts inside pair-chart patches holds "locally chart covered" everywhere, in
the sense of the Library's `IsLocallyChartCovered`
(`QuasiEtaleRigidity/RefinementGluing`). The theorem uses only the
commutativity `w : p ≫ f = q ≫ g`, not the pullback property, and involves
no smallness assumption.

## Declarations

- `InPairChartPatch f g p q W` (definition, a proposition): the chart `W` of
  `P` lies in a pair-chart patch, i.e. there is `c : PairChartData f g` with
  `range (chart W) ⊆ (c.patch p q).carrier`.
- `isLocallyChartCovered_inPairChartPatch w y`: under `w : p ≫ f = q ≫ g`,
  `(presentationOf P).IsLocallyChartCovered (InPairChartPatch f g p q) univ y`
  for every point `y`. It is the special case `Q := InPairChartPatch f g p q`
  of the theorem below.

## Main theorem

`isLocallyChartCovered_of_pairCharts (w : p ≫ f = q ≫ g) (Q) (hQ) (y)`:
suppose `Q` is a predicate on chart indices of `P` such that
`hQ : ∀ (c : PairChartData f g) W, range (chart W) ⊆ (c.patch p q).carrier → Q W`.
Then `(presentationOf P).IsLocallyChartCovered Q univ y` holds for every
point `y`. That is, there are finitely many charts containing `y`, all
satisfying `Q`, whose union contains a neighbourhood of `y`.

## Proof

Let `b = f (p y) = g (q y)`.

1. `isLocallyChartCovered_of_mem_nhds` (applied to `univ`) gives a finite set
   `K₀` of charts of `B` containing `b`, covering a neighbourhood `NB` of `b`.
2. For each `k ∈ K₀`, the inverse image `domainPreimage f (chartDomain k)` is
   an analytic domain of `U` containing `p y`. By
   `isLocallyChartCovered_analyticDomain` there is a finite set `MU k` of
   charts of `U`, all containing `p y` and lying in `f⁻¹(chart k)`, which
   cover `f⁻¹(chart k) ∩ NU k` for a neighbourhood `NU k` of `p y`. The same
   construction on `V` gives `MV k` and `NV k`.
3. Index by triples `(k, m, n)` with `k ∈ K₀`, `m ∈ MU k`, `n ∈ MV k`; there
   are finitely many. Each triple defines a `PairChartData` with
   `left = m`, `right = n`, `base = k`.
4. The set
   `N₀ = p⁻¹(⋂ₖ NU k) ∩ q⁻¹(⋂ₖ NV k) ∩ p⁻¹(f⁻¹ NB)` is a neighbourhood of
   `y`, by continuity of the underlying maps and finiteness of `K₀`. Every
   `z ∈ N₀` lies in some patch. First `f (p z) ∈ NB` lies in some chart
   `k ∈ K₀`. Then `p z ∈ f⁻¹(chart k) ∩ NU k` lies in some `m ∈ MU k`. By
   commutativity `g (q z) = f (p z)` lies in chart `k`, so `q z` lies in some
   `n ∈ MV k`.
5. Every patch is an analytic domain containing `y`, so it is locally chart
   covered at `y` (`isLocallyChartCovered_analyticDomain`), and its charts
   satisfy `Q` by `hQ` (`IsLocallyChartCovered.of_subset_pred`).
   `isLocallyChartCovered_of_cover` assembles the finitely many patches.
