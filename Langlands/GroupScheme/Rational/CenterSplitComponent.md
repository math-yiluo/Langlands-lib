# Actual scheme-center points and central point quotients

Author: Worker 101.

This is an internal construction from the published all-test `center`,
`IsCentral`, `rationalPoints.map`, and canonical `rationalPointTopology`
definitions. It adds no algebraic structure or compactness assumption to a
group scheme. Its purpose is to make the exact point quotient in WST-CEN-01
available before stating compactness.

For a group scheme `M` over `Spec F`, `schemeCenterPoints M` is precisely
`(center M).carrier (Over.mk (𝟙 _))`. Membership retains centrality after
every map of test schemes, including nonreduced test schemes. No smoothness,
connectedness, or identity-component operation is applied to the center.
`schemeCenterPoints_le_center` is the already proved inclusion into
`Subgroup.center (rationalPoints M)`. Equality with that abstract group center
is a separate mathematical target. `schemeCenterPointsToCenter` is the
inclusion homomorphism, with the identity map on ambient rational points.

For an actual group-scheme homomorphism `i : H ⟶ M` with `hi : IsCentral i`,
`centralRationalPointsMap i hi` sends a point `a` to
`⟨rationalPoints.map i a, hi _ a⟩`. Its range is
`centralRationalPointImage i hi`. The membership lemma identifies this range
with the points `z` for which an actual `a : rationalPoints H` satisfies
`rationalPoints.map i a = z.val`. The `eq_subgroupOf` lemma identifies it
with the ambient point-map range restricted to `schemeCenterPoints M`.
These lemmas follow by subtype extensionality. The commutativity instance
uses the published `commute_of_mem_center`; normality then follows from
commutativity.

`CentralPointQuotient i hi` is the group quotient of these two point groups.
For a split component one takes `H = A.toGrp` and
`hi = hA.isCentralSplitTorus.isCentral`. The definition neither constructs a
scheme quotient nor identifies its points with this point quotient.

When `F` has a topology and `M` is affine, `schemeCenterPointTopology M`
is the subgroup topology obtained after explicitly installing
`rationalPointTopology F M.X` on `rationalPoints M`.
`centralPointQuotientTopology i hi` is Mathlib's quotient topology for that
inherited topology. Neither definition installs a global topology instance.
No local-field, reductivity, splitness, or compactness premise is required
for these constructions.

The notation for the central maximal split torus is the one already sourced
in `Rational.Characters`: Renard V.2.1, printed p.104 / PDF p.110 (9 July
2026 edition), and Waldspurger I.1, printed pp.238–239 / PDF pp.4–5. The
present contribution is derived infrastructure for those published definitions,
not a new assertion that the two notions of center coincide.
