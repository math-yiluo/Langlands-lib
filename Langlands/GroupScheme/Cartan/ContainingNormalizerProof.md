# Normalizers of smooth subgroups containing a torus centralizer

Workers 615 and 218. This proof develops the Lie algebra argument for Milne,
*Algebraic Groups* (2017), Lemma 17.47, printed p.366. The registered official
2017 errata snapshot (2026-11-02) contains no correction to that lemma.

The theorem
`Langlands.GroupScheme.cartanContainingNormalizer.{u}` has exactly the type
`Langlands.GroupScheme.CartanContainingNormalizerStatement.{u}`. It imports
the published proposition without changing its hypotheses or dependencies.
The field, group schemes, splitting extension and algebraic closure all lie in
the arbitrary common universe `u`.

## Implemented argument

The implemented split, algebraically closed argument uses the published regular
torus point decomposition: every vector is a difference under the adjoint action
plus a zero weight vector. The difference is a commutator of a normalizer point
with a torus point in the subgroup. The zero weight vector centralizes the torus
on every test scheme. Both therefore belong to the subgroup. The argument applies
to a possibly non-smooth normalizer and does not require maximality of the torus.

The open immersion consequence factors the torus through the represented
normalizer, lifts each actual dual-number identity-kernel point to the subgroup,
and cancels the closed normalizer embedding. The published full Lie algebra
criterion for smooth closed subgroups then gives openness.

The arbitrary-field argument chooses a splitting field of the witnessing torus
and then an algebraic closure of that field. Splitting persists in this tower.
The all-test torus centralizer and normalizer commute with base change, as do
represented subgroup ranges. The split result thus makes the base-changed
subgroup embedding an open immersion. Faithfully flat quasi-compact descent
reflects this property back to the original field.

Finally, a Cartan subgroup is the centralizer of its witnessing maximal torus.
Containment gives the centralizer hypothesis above. The subgroup factors
through its represented normalizer; its open embedding and smoothness imply
smoothness of the normalizer by the published smooth-open-subgroup criterion.
This proves exactly `CartanContainingNormalizerStatement` in every universe.

The internal helpers in `CartanContainingNormalizer` are:

- `lie_mem_range_of_split`: when a split torus maps into an affine, locally
  finite type group `N`, the image of `N` normalizes a subgroup `H`, and the
  ambient torus centralizer is contained in `H`, every actual dual-number
  identity-kernel point of `N` maps into `H`. Here `k` is algebraically closed;
  neither smoothness nor connectedness of `N` is assumed.
- `isOpenImmersion_of_split`: if `G` is affine and locally of finite type,
  `H` is smooth and closed, and `N` is a closed representative of its
  normalizer, the preceding lifting proves that every factor `H → N` is
  open. The torus source is split over the algebraically closed field.
- `isOpenImmersion_of_torus`: the same openness conclusion holds for an
  arbitrary torus over an arbitrary field, by the field descent above.

These are internal consequences of the imported results, with no maximality
or connectedness premises. The final theorem uses the witnessing torus from
`IsCartanSubgroup`; the ambient smoothness in the published target supplies
local finite type. It retains every hypothesis of that exact target.

## Sources and provenance

Milne's source is registered as `milne-2017-algebraic-groups`; the official
2017 errata snapshot is registered as
`milne-2017-algebraic-groups-errata-2026-11-02`. The statement correspondence,
including the smooth affine convention and the open immersion formulation,
is recorded in [ContainingNormalizerStatement](ContainingNormalizerStatement.md).
The proof here replaces Milne's quotient invariant and dimension argument
with the actual-point commutator calculation.

The main imported proof inputs are the regular torus weight decomposition in
[ClassFunctionsTorusDensity](../Rational/ClassFunctionsTorusDensity.md), the
zero weight centralizer calculation in [TorusCentralizer](../Lie/TorusCentralizer.md),
the [full Lie algebra openness criterion](../Lie/FullLieOpenSubgroup.md), and
[smoothness from a smooth open subgroup](../Lie/SmoothOpenSubgroup.md).
All subgroup containment and normalization calculations use the all-test
subgroup functors, including after field extension.
