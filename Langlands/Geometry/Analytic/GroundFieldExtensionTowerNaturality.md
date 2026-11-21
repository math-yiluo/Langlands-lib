# Naturality of the tower comparison for ground field extension

Let `K → L → M` be a tower of complete ultrametric normed fields with the
three normed algebra structures and `IsScalarTower K L M`. The three fields,
the original ambient spaces and the chart indices have independent
universes. `compatibleFunctor K M` is the Library's ground field extension
functor on presented `K`-affinoid atlases with compatible strong maps. The
composite `compatibleFunctor K L ⋙ compatibleFunctor L M` extends first to
`L` and then to `M`. Both functors land in the same category of presented
`M`-affinoid atlases of widths `{u'', max u'' w, w}`. Here `u''` is the
universe of `M` and `w` the original index universe.

`towerHomeomorph_pointMap` says that the glued tower homeomorphisms
intertwine the point maps. Take a compatible strong map `f : A ⟶ B` and
extend it directly from `K` to `M`. Composing its point map with the tower
homeomorphism of `B` gives the tower homeomorphism of `A` followed by the
point map of the successive extension of `f`. The proof works on a chart
`i` of `A` with an admissible target index `j` of `f`. There both point
maps are given by the target chart at `j` composed with the spectrum map of
the extended bounded pullback, by the Library's `pointMap_chart`. The
spectrum maps are then intertwined by the naturality of the affinoid tower
homeomorphism, applied to the original bounded pullback of `f` at `(i, j)`.

`towerCompatibleHom_natural` is the equality of compatible strong maps

`towerCompatibleHom A ≫ (L → M)((K → L) f) = (K → M) f ≫ towerCompatibleHom B`

in diagrammatic order, written with `CompatibleStrongHom.comp`. It includes
every bounded pullback, not only the underlying continuous maps. The base
maps agree by the point-map statement. For the pullbacks the proof uses
`CompatibleStrongHom.ext_of_pullback`: it suffices to compare one admissible
target for each source chart. The source chart `i` is sent to an admissible
target `j` of `f`, and the index `j` is admissible for both composites.
Bounded pullbacks run contravariantly, from the target chart algebra at `j`
to the source chart algebra at `i`. Both composites start at the successive
target chart algebra at `j` and end at the direct source chart algebra at
`i`.

- The first composite applies the successive extension of the bounded
  pullback `f.pullback i j` first, landing in the successive source chart
  algebra at `i`. It then applies `towerChartEquiv` at `i`, landing in the
  direct source chart algebra at `i`. In Lean this is
  `(towerChartEquiv i).comp (map L M (map K L (f.pullback i j)))`.
- The second composite applies `towerChartEquiv` at `j` first, landing in
  the direct target chart algebra at `j`. It then applies the direct
  extension of `f.pullback i j`, landing in the direct source chart algebra
  at `i`. In Lean this is `(map K M (f.pullback i j)).comp (towerChartEquiv j)`.

Here `g.comp h` applies `h` first, as for bounded algebra maps in the
Library. Both composites are computed by `comp_pullback` and the
matching-index formula `towerCompatibleHom_pullback_same`. They agree by the
bounded-map naturality `towerEquiv_naturality` of the affinoid tower
equivalence, applied to the original bounded pullback `f.pullback i j`.

`towerIso P` packages, for a compatible presentation `P`, the comparison
`towerCompatibleHom` and its inverse `towerCompatibleInv` as an isomorphism
between `(compatibleFunctor K M).obj P` and the successive extension of `P`.
The two inverse laws are `towerCompatibleHom_comp_inv` and
`towerCompatibleInv_comp_hom`. `towerIso_hom` records the forward component.
`towerNatIso` is the natural isomorphism

`compatibleFunctor K M ≅ compatibleFunctor K L ⋙ compatibleFunctor L M`

built by `NatIso.ofComponents` from these isomorphisms. Its naturality
square is `towerCompatibleHom_natural`, read in the opposite direction.
`towerNatIso_hom_app` records that its components are the tower
comparisons. No global Hausdorffness, nontrivial valuation or finite degree
is assumed.

## Provenance and scope

This is a derived comparison on the Library's actual scalar-extension
functor. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), §1.4, printed p. 30 (PDF p. 27), constructs ground field extension
by gluing. Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces*, 24 February 2009 preprint, Theorem 2.3.5, printed and PDF p. 13,
states that the natural analytification comparisons are transitive under
further ground field extension. This module proves the transitivity of
ground field extension itself, at the level of presented atlases and
compatible strong maps. It does not treat the saturated or localized
categories. Nor does it state the transitivity square with
analytification, the compatibility of `towerNatIso` with the comparisons of
Theorem 2.3.5, or associativity for a tower of four fields.
