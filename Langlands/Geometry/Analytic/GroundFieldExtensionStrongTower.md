# Compatible strong comparison of direct and successive ground field extension

Let `K → L → M` be a tower of complete ultrametric normed fields with the
three normed algebra structures and `IsScalarTower K L M`. Let `a` be an
indexed `K`-affinoid atlas. `D` is the Library's actual presented atlas of
the scalar extension of `a` from `K` to `M`. `S` is the actual presented
atlas of the scalar extension from `L` to `M` of the actual `K → L`
extended atlas. The three fields, the original ambient space and the chart
index have independent universes, and both presentations have the same
widths. Both atlases are indexed by the original chart index.

## Generic assembly

The private structure `ChartwiseComparison A B` collects, for two presented
`F`-affinoid atlases, the following data:

- a homeomorphism of the ambient spaces;
- an equivalence of chart indices;
- for each source index `i`, a bounded `F`-algebra equivalence from the
  target algebra at the matching index to the source algebra at `i`;
- the chart formula: on chart `i`, the homeomorphism is the target chart at
  the matching index composed with the spectrum homeomorphism of that
  equivalence;
- for every pair of source containments and corresponding target
  containments, the bounded equivalences intertwine the two actual bounded
  restrictions.

From these data it builds a `StrongHom`. Its base map is the given
homeomorphism. At every admissible pair `(i, j)` its bounded pullback is the
target restriction from the matching index of `i` to `j`, followed by the
chart equivalence at `i`. The matching index is admissible because the
homeomorphism carries chart `i` onto the matching target chart. The chart
equation follows from the restriction chart formula and the given chart
formula. The restriction equation follows from the given intertwining and
composition of target restrictions. Compatibility of the pullbacks is
coherence of the identity strong map of the target, composed with the chart
equivalence. The quasi-isomorphism property holds: the base map is a
homeomorphism, and at every admissible pair the image locus is the matching
target chart, which the target restriction represents inside chart `j`.
Composing with a bounded equivalence preserves this representation. At the
matching index the pullback is the chart equivalence itself, by
`restriction_id`.

A private lemma `hom_comp_hom` compares two such assemblies `c : A → B` and
`d : B → A`. Its hypotheses are that `d`'s homeomorphism inverts `c`'s on
points, and a chart condition at each source index `i`. Let `k` be the
index of `A` matched to `i` by `c` and then by `d`. The condition says: apply
the restriction of `A` from chart `i` to chart `k`, then `d`'s chart
equivalence at the matching index, then `c`'s chart equivalence at `i`.
The result is the identity on every element of the algebra at `i`. Under these
hypotheses the composite compatible map is the identity compatible map of
`A`, with the same base map and the same bounded pullbacks. The proof uses
`ext_of_pullback` at the chain `i → (matching index of i) → i`. The middle
containment follows from the two image-of-chart formulas and the point
inverse law. The composite pullback is computed by `comp_pullback`, and the
identity pullback is `restriction_id`. The lemma works with abstract
endpoints, so the kernel does not reduce the actual quotient atlases. Four
private lemmas state the hypotheses at the tower comparison with their
exact types.

## The tower comparison

`towerChartEquiv` is `towerEquiv` on the original chart algebra at each
index. It is the bounded `M`-algebra equivalence from the successive to the
direct extended chart algebra. `towerChartEquiv_restriction` proves that
these equivalences intertwine the actual restrictions of `S` and `D` for
every containment, from the bounded-map naturality of `towerEquiv`. It
applies that naturality to the original bounded restriction of `a`, which
exists by the containment criterion `range_chart_subset_iff`.
`towerAdmissible_iff` identifies the admissible pairs of the comparison with
containments of successive charts.

`towerCompatibleHom` is the `CompatibleStrongHom D S` assembled from the
homeomorphism `towerHomeomorph`, the identity of the original index and
`towerChartEquiv`. It is stated with these properties:

- `towerCompatibleHom_apply`: the base map is the actual glued tower
  homeomorphism;
- `towerCompatibleHom_isQuasiIso`: the comparison is a strong
  quasi-isomorphism, so each admissible bounded pullback represents the
  full inverse-image domain, not only matching charts;
- `towerCompatibleHom_pullback`: each admissible pullback is the successive
  restriction followed by the chart equivalence (definitional);
- `towerCompatibleHom_pullback_same`: at the matching index the pullback is
  the full bounded `towerEquiv`.

`towerChartEquiv_symm_restriction` proves the restriction intertwining for
the inverse chart equivalences, from `towerChartEquiv_restriction` applied
to inverse images. `towerCompatibleInv` is the `CompatibleStrongHom S D`
assembled from the inverse homeomorphism, the identity of the original
index and the inverse chart equivalences. Its chart formula is
`towerHomeomorph_symm_chart`. It is stated with these properties:

- `towerCompatibleInv_apply`: the base map is the inverse homeomorphism;
- `towerCompatibleInv_isQuasiIso`: it is a strong quasi-isomorphism;
- `towerCompatibleInv_pullback_same`: at the matching index the pullback is
  the inverse bounded tower equivalence;
- `towerCompatibleHom_comp_inv` and `towerCompatibleInv_comp_hom`: the two
  composites are the identity compatible maps of `D` and of `S`. So the
  comparison is an isomorphism in the category of compatible strong maps,
  including all bounded pullbacks.

No global Hausdorffness, nontrivial valuation or finite degree is assumed.

## Provenance and scope

This is a derived comparison on the Library's actual quotient chart
construction. Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), §1.4, printed p. 30 (PDF p. 27), constructs ground field
extension by gluing. Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces*, 24 February 2009 preprint, Theorem 2.3.5, printed and
PDF p. 13, states the transitivity of the natural analytification
comparison under further ground field extension. This module gives only
the object-level comparison of the two extended presented atlases as a
compatible strong quasi-isomorphism with its compatible inverse. Naturality
in compatible maps is proved in `GroundFieldExtensionTowerNaturality`. The
localized comparison and the transitivity square with analytification are
not stated here.
