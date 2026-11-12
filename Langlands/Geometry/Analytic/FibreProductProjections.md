# The projections of a fibre product as compatible strong maps

Author: Worker 21.

This module turns the two projections of the fibre product `X ×_S Y` (module
`FibreProductAtlas`) into compatible strong maps:

- `FibreProduct.fstHom f g hA hB : CompatibleStrongHom (presentation f g hA hB) A`;
- `FibreProduct.sndHom f g hA hB : CompatibleStrongHom (presentation f g hA hB) B`.

It also proves the commutative square `fstHom ≫ f = sndHom ≫ g` in the
Library's category of compatible strong maps (`fstHom_comp`).

The hypotheses are those of `FibreProductAtlas`: `X`, `Y`, `S` Hausdorff, and
the atlases of `X` and `Y` contain all local affinoid domains. In addition,
the three presentations lie in `AffinoidAtlasPresentation.{u, u, u} K`. The
fibre product presentation lies in `AffinoidAtlasPresentation.{u, max u w,
max u w} K`. A compatible strong map needs source and target in the same
universes, so the universes must agree. All declarations lie in
`Langlands.Analytic`.

## Original source and derived provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`, proof of
Proposition 1.4.1, printed p.30 / PDF p.27: "It is easy to see that the
canonical projections Y' → Y and Y' → X' are morphisms of Φ_k-analytic spaces
and that Y' is a fibre product of Y and X' over X in the category Φ_k-𝒜n."

The projections and their bounded pullbacks below are derived. The pullback
to a chart of `X` containing the image of a fibre product chart is the first
pushout leg, moved to that chart by the Library's target chart change. The
universal property of the fibre product is not proved here (see Scope).

## General chart-change lemmas

In `IndexedAffinoidAtlas`:

- `isMapChartChange_comp_restriction`: `φ ∘ res(j, j')` is the chart change of
  `φ` from `j` to `j'` (Library `changeMapChart_of_subset`).
- `isMapChartChange_changeMapChart`: two chart changes of one map are chart
  changes of each other. Combine the Library's reverse chart change
  (`changeMapChart_reverse_isMapChartChange`) with `IsMapChartChange.trans`.

## The projections

For an index `T` of the fibre product atlas, with chosen pair `T.rep`:

- `fstPullback f g T i h : O(V_i) → O(T)` for a chart `V_i` of `X` containing
  the first projection of the chart of `T`. It is the chart change of the first
  leg `leftMap` of the pair from `V_{T.rep}` to `V_i`.
- `fstHom f g hA hB`: base map `fst`, chosen target `V_{T.rep}`, pullbacks
  `fstPullback`.
  - The chart equation is the Library's `changeMapChart_chart`.
  - The restriction equation holds because both composites are chart changes
    of the first leg of `T.rep`: one by `isMapChartChange_rangeRestriction_left`
    of `FibreProductRestriction`, the other by
    `isMapChartChange_comp_restriction`. Chart change is unique
    (`eq_changeMapChart`).
  - Compatibility (`HasLocallyCompatiblePullbacks`, equivalent to coherence)
    is `isMapChartChange_changeMapChart`.
- `sndPullback`, `sndHom`: the same for the second leg and `Y`.

## The commutative square

`fstHom_comp`: `(fstHom f g hA hB).comp f = (sndHom f g hA hB).comp g` as
compatible strong maps. The base maps agree by `baseMap_fst`. The Library's
`CompatibleStrongHom.ext_of_pullback` then needs agreement of one admissible
pullback on each chart. On the chart of `T`, over the base chart of `T.rep`,
the Library's `comp_pullback` computes the two composites as
`leftMap ∘ leftBase` and `rightMap ∘ rightBase` (chart change to the original
chart is the identity, `changeMapChart_self`). These agree by the pushout
condition.

## Scope

Not proved here: the universal property of the fibre product. A map into the
fibre product from a space `Z` exists in general only after refining the atlas
of `Z`, that is, as a morphism of the localized category. The image of the
fibre product in the localized category and base change of étale morphisms are
also not treated.
