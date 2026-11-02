# Restricting a strict-test representation to a rational domain

Author: Worker 1010.

Fix a normed field K with ultrametric absolute value and presented strict
affinoid algebras P and Q over K. Write `M(P)` for the Banach spectrum of P.

## Restriction along a composite

The imported `StrictTestDomain.comap_comp_apply` from `CalculusProof` records that restricting a point along a
composite `j ∘ i` equals restricting first along j and then along i. Both
sides are the same function on P, so the proof is extensionality of points.

## Rational quotients

The remaining results assume K complete. Let `d : RationalData K P` be the
published rational data, with rational quotient `d.algebra` and base map
`d.baseMap : P → d.algebra`.

- `RationalData.comap_baseMap_injective`: restriction along the base map is
  injective on `M(d.algebra)`. This is the published
  `RationalLocalization.comap_baseMap_injective`, applied to the denominator,
  numerators and unit-ideal hypothesis of d.
- `RationalData.range_comap_baseMap`: the image of that restriction is exactly
  `d.locus`. This is the second component of the published
  `StrictTestDomain.rationalRepresentation`.
- `RationalData.isClosed_locus`: `d.locus` is closed, the first component of
  the same published theorem.

## Restricting a representation

`RationalData.represents_comparison` assumes that the bounded map
`i : P → Q` represents `U ⊆ M(P)` for strict tests, in the sense of the
published `StrictTestDomain.Represents`. It concludes that the published
comparison map `d.comparison i` from `d.algebra` to the pulled-back rational
quotient `(d.pullback i).algebra` represents the inverse image of U under
restriction along `d.baseMap`.

The proof combines three published facts:

- `RationalData.pullback_represents`: the base map of the pulled-back rational
  quotient represents the inverse image of `d.locus` under restriction along
  `i`;
- `represents_comp_inter`, applied to this and to the representation of U by
  `i`, using that `d.locus` is closed: the composite of `i` with that base map
  represents `U ∩ d.locus`;
- `RationalData.comparison_comp_baseMap`: the comparison map composed with
  `d.baseMap` equals the pulled-back base map composed with `i`.

The three conditions of `Represents` are then checked as follows.

- Closedness: the inverse image of the closed set U under the continuous
  restriction map is closed.
- Image: a point z of the pulled-back algebra restricts to a point of
  `d.algebra` whose restriction to P equals the restriction of z along the
  composite, which lies in U. Conversely, take x in `M(d.algebra)` whose
  restriction to P lies in U. That restriction also lies in `d.locus`, so it
  is the restriction of some point z along the composite. Injectivity of
  restriction along `d.baseMap` then shows that z restricts to x along the
  comparison map.
- Universal property: let φ from `d.algebra` to a strict test algebra have
  image in the inverse image of U. Then `φ ∘ d.baseMap` has image in
  `U ∩ d.locus`, so it factors uniquely through the composite. The factor also
  satisfies the required equation after the comparison map, because maps out
  of `d.algebra` are determined by their composite with `d.baseMap`
  (published `RationalData.hom_ext`). Uniqueness follows the same way.
