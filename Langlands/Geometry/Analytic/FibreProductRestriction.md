# Restrictions between fibre product charts with included ranges

Author: Worker 21.

The module `FibreProductChartSystem` glues the fibre product `X ×_S Y` from the
charts `V ×_W U` of pairs of charts with a common base chart. Its restriction
maps exist only for componentwise inclusions of pairs. An atlas of the glued
space also needs restrictions whenever one chart range lies in another, even
when the factor charts are not included in each other. This module constructs
those restrictions and proves the atlas laws for them:

- the chart equation;
- the universal property of the restriction for the contained range;
- the identity and composition laws.

All declarations lie in `Langlands.Analytic`. The setting is that of
`FibreProductChartSystem`: affinoid atlas presentations `A`, `B`, `C` and
compatible strong maps `f : A → C`, `g : B → C`. No saturation or Hausdorff
hypothesis is used.

## Original source and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, proof of
Proposition 1.4.1, printed p.30 / PDF p.27: "the canonical morphism
V' := V ×_U U' → Y' identifies V' with an affinoid domain in Y'", and the sets
`V ×_U U'` carry "an evident Φ_k-affinoid atlas". Berkovich gives no further
detail. The construction below is derived. It moves the two pushout legs to
the containing chart by the Library's target chart change for arbitrary
affinoid tests (`changeMapChart`), and assembles them by the pushout property.

## General chart-change lemmas

In `IndexedAffinoidAtlas`:

- `changeMapChart_congr`: chart change depends only on the map, not on the
  proof of the image condition.
- `isMapChartChange_restriction`, `changeMapChart_restriction`: for a chart `m`
  contained in charts `i` and `j`, the map `φ ∘ res(m, j)` is the chart change
  from `i` to `j` of `φ ∘ res(m, i)`. The proof is the Library's
  `originalChartRestriction_test_overlap`.

## The restriction

In `FibreProduct`, for pairs `p`, `q` whose chart ranges satisfy
`range(chart p) ⊆ range(chart q)`:

- `leftPoint_mem_of_range_subset`, `rightPoint_mem_of_range_subset`: the
  projections of points of the chart of `p` lie in the factor charts of `q`
  (`mem_range_chart_iff`).
- `condition_of_changeMapChart`: let two pairs of legs be related by chart
  changes in `X` and in `Y`. If the first pair satisfies the pushout condition
  over the base chart of `p`, the second satisfies it over the base chart of
  `q`. Strong maps preserve chart changes (Library
  `mapAffinoidChart_isMapChartChange_of_coherent`), so both sides over the
  base of `q` are chart changes in `S` of the same map; the Library's
  uniqueness `eq_changeMapChart` identifies them.
- `rangeLeft`, `rangeRight`: the legs of `p` changed to the factor charts of
  `q`. `rangeCompat` is the pushout condition over the base of `q`.
- `rangeRestriction h : O(q) → O(p)`: the pushout lift of these legs.
  `rangeRestriction_comp_leftMap` and `rangeRestriction_comp_rightMap` are the
  lift identities.

## Atlas laws

- `restriction_comp_rangeRestriction`: on a common subpair `m` of `p` and `q`,
  composing with the chart system restriction gives the chart system
  restriction `res(m, q)`. On both pushout legs this is
  `changeMapChart_comp` followed by `changeMapChart_restriction`.
- `chart_rangeRestriction`: the chart of `q` sends the pullback of a point `x`
  of the chart of `p` to the same point as the chart of `p`. The two chart
  points of the glued space are pullbacks of one point of a common subpair
  (`chart_eq_iff`), and the previous lemma applies.
- `rangeRestriction_self`: for `p = q` the restriction is the identity
  (`changeMapChart_self`).
- `rangeRestriction_comp`: restrictions compose. On each leg the composite is
  a chart change of the leg of `p` (`IsMapChartChange.comp` and `.trans`), and
  chart change is unique.
- `isMapChartChange_rangeRestriction_left` and `_right`: the range restriction
  followed by a chart change of a leg of `q` is a chart change of the
  corresponding leg of `p`. This is used for the projections of the fibre
  product.
- `rangeRestriction_universal`: a bounded map `φ : O(q) → R` to a presented
  affinoid test, whose points land in the chart of `p`, factors uniquely
  through the restriction. The factorization is the pushout lift of the chart
  changes of `φ ∘ leftMap` and `φ ∘ rightMap` to the factor charts of `p`.
  Their compatibility is `condition_of_changeMapChart`. Existence and
  uniqueness reduce on each leg to `changeMapChart_self` and to the reverse
  chart change (`changeMapChart_reverse_isMapChartChange`).

## Scope

The atlas itself, which needs the net property and the Hausdorff property of
the glued space, is assembled in `FibreProductAtlas`.
