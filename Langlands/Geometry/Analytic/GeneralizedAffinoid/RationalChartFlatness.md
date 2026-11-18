# Flatness of rational chart restrictions

This module proves that the structural map of every Library rational chart
`d : RationalChart K A` is flat as a homomorphism of the underlying commutative
rings. Here `A` is a presented affinoid algebra over a complete ultrametric
normed field `K`, and the chart may have any number of fraction coordinates and
any positive radii. No condition is placed on the valuation of `K`.

The input for one fraction coordinate is
`flat_rationalPresentation_baseMap` from `RelativeSeriesFlatness`. Several
fractions are reduced to one fraction at a time. Charts are compared through
their loci by `Domain.flat_baseMap_of_locus_eq` from
`DomainFlatnessReduction`: two full domains with the same locus have
isomorphic algebras over `A`, so either both structural maps are flat or
neither is.

## Declarations

All declarations are in namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`. The locus of a
chart with denominator `g`, numerators `f j` and radii `r j` is the set of
spectrum points `x` with `x(f j) ≤ r j · x(g)` for all `j`.

- `flat_extendDomain d U hd hU`: if the chart `d` has a flat structural map
  and the full domain `U` over `d.algebra` does too, then so does the composed
  domain `d.extendDomain U` over `A`.
- `range_spectrumMap d`: the range of the chart's spectrum map is its locus.
- `extendDomain_pullback_locus L e`: the locus of
  `L.extendDomain (pullback L.baseMap e).toDomain` is `e.locus ∩ L.locus`.
- `flat_baseMap_of_locus_eq_inter d L e h hL he`: if
  `d.locus = e.locus ∩ L.locus`, the chart `L` has a flat structural map, and
  the pullback of `e` along `L.baseMap` has a flat structural map, then `d` has
  a flat structural map.
- `flat_baseMap_of_arity_eq_one d h`: charts with exactly one fraction
  coordinate have flat structural maps.
- `generatesUnitIdeal_of_isUnit g f hg`: if the class of `g` is a unit, then
  `g` and any family `f` generate the unit ideal.
- `flat_baseMap_of_isUnit_denominator m B d hm hu`: if `d` has `m` fraction
  coordinates and the class of its denominator is a unit in `B`, then `d` has
  a flat structural map.
- `pos_denominator_of_mem_locus d hx`: every point of a chart locus takes a
  positive value on the denominator.
- `flat_baseMap d`: every rational chart has a flat structural map.

## Proofs

**Composition and loci.** The structural map of `d.extendDomain U` is the
composite of `U.baseMap` with `d.baseMap`, so `flat_extendDomain` is
`RingHom.Flat.comp`. The range of a chart's spectrum map is its locus, which
is part of the chart's `Represents` property. The Library lemmas
`extendDomain_locus`, `toDomain_locus` and `pullback_locus` show that the
locus of `L.extendDomain (pullback L.baseMap e).toDomain` is the image under
`L.spectrumMap` of the preimage of `e.locus`. By
`Set.image_preimage_eq_inter_range` this image is `e.locus ∩ L.locus`. In
`flat_baseMap_of_locus_eq_inter` this composed domain is flat by
`flat_extendDomain` and has the same locus as `d.toDomain`, so
`Domain.flat_baseMap_of_locus_eq` gives flatness of `d`.

**One fraction.** A chart with arity `1` is, after destructuring and
substituting the arity, the scalar rational presentation with one fraction
coordinate. Its flatness is `flat_rationalPresentation_baseMap`.

**Unit denominators.** The proof is by induction on the arity `m`, for all
presented affinoid algebras `B` at once.

- If `m = 0`, the locus condition is vacuous, so the locus is the whole
  spectrum. The chart's locus therefore equals that of the whole domain
  `Domain.whole K B`, whose structural map is the identity, which is flat.
- If `m = k + 1`, the proof splits `d` into two charts with the same
  denominator. The chart `d₁` keeps only the fraction coordinate `0`, and `d'`
  keeps the coordinates `1, …, k` with their radii. Both are valid charts by
  `generatesUnitIdeal_of_isUnit`. The locus of `d` is `d'.locus ∩ d₁.locus`
  by splitting the index `j` into `0` and successors. The chart `d₁` is flat
  by the one-fraction case. The pullback of `d'` along `d₁.baseMap` has `k`
  fraction coordinates, and by `pullback_denominator_class` its denominator
  class is the image of a unit under a ring map, so it is again a unit. It is
  flat by the induction hypothesis over `d₁.algebra`. The lemma
  `flat_baseMap_of_locus_eq_inter` then gives flatness of `d`.

**Positivity on the locus.** If `x(g) = 0` at a point `x` of the locus, then
`x(f j) ≤ r j · 0 = 0` for every `j`. So `g` and all `f j` lie in the kernel
of `x`. Since they generate the unit ideal, the kernel would contain `1`, but
`x(1) = 1`.

**General charts.** The imported `RationalChart.exists_pos_le_denominator` supplies a
positive uniform lower bound `c` for the denominator on `d.locus`, including the empty
locus. It uses compactness, continuity of evaluation and the unit-ideal condition.
Let `L` be the one-fraction chart with denominator `g`, numerator `1`
and radius `c⁻¹`. Its locus is `{x | 1 ≤ c⁻¹ · x(g)} = {x | c ≤ x(g)}`, which
contains `d.locus`, so `d.locus = d.locus ∩ L.locus`. The chart `L` is flat
by the one-fraction case. In `L.algebra` the defining equation of the fraction
`T` reads `g · T = 1`, so the class of `g` is a unit there. Hence the pullback
of `d` along `L.baseMap` has a unit denominator class and is flat by the
unit-denominator case. Applying `flat_baseMap_of_locus_eq_inter` with `e = d`
finishes the proof.

## Provenance

The reduction is internal to this project. It follows the familiar pattern of
writing a rational domain as a Laurent domain `{c ≤ |g|}` on which `g` is
invertible, and then cutting out one fraction coordinate at a time. Berkovich,
*Spectral theory and analytic geometry over non-Archimedean fields* (1990),
Proposition 2.2.4(ii), proves flatness of affinoid-domain restrictions
differently. It treats the strictly affinoid case through
Bosch–Güntzer–Remmert 7.3.2/6 and reduces the general case by extending the
ground field. The present route needs no strictness and no nontrivially valued
ground field.
