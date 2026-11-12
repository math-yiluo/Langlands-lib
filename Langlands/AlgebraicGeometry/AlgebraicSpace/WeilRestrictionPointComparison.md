# Weil restriction point comparison with an explicit vector topology

Original construction: Worker 111. Continuous scalar-action generalization: Worker 113.

This module constructs `ringWeilRestrictionPointHomeomorph`, a canonical
homeomorphism on rational points of a Weil restriction, under explicit geometric
and topological hypotheses. It is an auxiliary result toward Conrad's
Proposition 5.11(1), printed p.18 of *Weil and Grothendieck approaches to adelic
points* (December 31, 2011). It does not prove the published
`HenselianWeilRestrictionPointHomeomorphStatement`.

## Scope and inputs

Let `K` and `K'` be nontrivially normed fields, with their specified `Algebra K K'` and
`ContinuousSMul K K'` structures, `FiniteDimensional K K'` and **`IsModuleTopology K K'`**. Assume that both are
henselian in the published `IsHenselianValuedField` sense. Let `Y'` be an
algebraic space over `Spec K'`, and supply:

- `hY' : IsQuasiSeparatedLocallyFiniteType K' Y'`;
- a proof `h` that its Weil restriction sheaf is an algebraic space;
- `hY : IsQuasiSeparatedLocallyFiniteType K (ringWeilRestrictionSpace K K' Y' h)`.

The construction has underlying equivalence exactly
`ringWeilRestrictionBasePointsEquiv K K' Y' h` and uses the independently defined
etale-chart topologies over `K` and `K'`. The theorem
`isHomeomorph_ringWeilRestrictionBasePointsEquiv` records its `IsHomeomorph`
property. No local separatedness, completeness, or separability is assumed;
the module topology is an explicit additional assumption. Representability,
quasi-separatedness, local finite type of the restriction, and that topology
assumption are not established here.

The separate forward-continuity theorem
`continuous_ringWeilRestrictionBasePointsEquiv` requires only the algebra structure and continuous scalar multiplication,
henselianity of `K'`, the input `hY'`, and representability `h`. It needs neither
finite dimensionality nor the module topology nor henselianity of `K`.

## Algebraic constructions

`ringWeilRestrictionSchemeAdjoint` converts a presheaf map from an actual
`R`-scheme `U` to a Weil restriction into a map from `U` base changed to `R'`
to the original algebraic space. It is constructed by two applications of
Yoneda's equivalence. Its section formula is proved in
`ringWeilRestrictionSchemeAdjoint_apply`. These constructions work over arbitrary
commutative rings with an algebra structure.

`ringPointBaseChangeEquiv_basePoint` identifies extension of a rational scheme
point with precomposition of its base change by `weilRestrictionBaseTestIso`.
The proof checks both projections of the actual scheme pullback; the first
projection uses the tensor multiplication isomorphism and the second is the
structure-map identity. Together with presheaf functoriality this proves
`ringWeilRestrictionBasePointsEquiv_schemePointsMap`, the pointwise compatibility
of adjunction with the canonical space-point identification.

For a finite projective algebra extension and an affine scheme `U'` locally of
finite type, `ringWeilRestrictionAffineSchemeMap` applies a map `h_U' -> Y'` to
the published `affineWeilRestrictionCounit` and then uses Yoneda to obtain a map
from `affineWeilRestriction R R' U'` into the restriction sheaf. Its point
compatibility with the published affine homeomorphism is
`ringWeilRestrictionBasePointsEquiv_affineSchemeMap`. Naturality of the input
map and the published `affineWeilRestrictionComparison_basePoint` prove this
identity. This does not require proving an isomorphism between representing
schemes or preservation of etaleness by Weil restriction.

## Implemented topology proof

For forward continuity, the final etale-chart topology reduces the claim to
maps from finite-type scheme charts of the restriction. The adjoint of such a
chart is a scheme map over `K'`. Extension of its rational scheme points to `K'`
is continuous by the published coefficient-change and base-change theorems.
The published `continuous_schemePointsMap` makes the adjoint map continuous
into `Y'(K')`. The compatibility identity above identifies this composite with
the required chartwise map.

For inverse continuity, use all affine etale charts of `Y'`. Every point lifts
to one by `exists_affine_chart_pointMap_eq`. Their point maps are open by
`EtaleFiniteTypeChart.isOpenMap_pointMap`, including for spaces that are not
locally separated. For each such chart, the composite of its point map with
the inverse equivalence is the affine point homeomorphism's inverse followed
by the map on points induced by `ringWeilRestrictionAffineSchemeMap`.
The affine homeomorphism uses `IsModuleTopology K K'`; continuity of the latter
map follows from `continuous_schemePointsMap` using `hY`.
A preimage of an open set is the union of its open images under these chart
maps, and is therefore open. The two continuity results define the displayed
homeomorphism. Continuous scalar multiplication supplies continuity of the
algebra map, which is the only interaction between the two field topologies
used in forward continuity. No equality of the two norms on the smaller
field is required. This generalization permits the original separately
normalized norms on ramified completed fields; it does not change either
field topology or point map.

## Provenance

This is a derived construction using the published affine Weil restriction,
Yoneda, actual scheme base change and henselian chart-topology results. Its
source motivation is Conrad, Proposition 5.11(1) and its proof, printed p.18,
registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The implemented route uses continuous scheme maps and open surjective chart
families rather than local homeomorphisms of charts. The explicit module-topology
input is retained from `affineWeilRestrictionPointHomeomorph` and is not supplied
by the printed statement. This auxiliary construction does not discharge the
assigned unchanged exact target or alter its published Lean/Markdown pair.

The continuous scalar-action generalization is internal: the same implemented
proof uses continuity of the original algebra map, not norm preservation.
The literature passage above is motivation for the original construction,
not a claim that this precise generalization is stated there.
