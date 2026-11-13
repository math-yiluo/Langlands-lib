# Complete NPC metric on the maximal-unramified building

This pair defines the metric data needed for a fixed-point argument on the exact
building used by `UnramifiedTwistedChamberStatement`, and states their existence.
`UnramifiedBuildingMetricStatement.{u}` is an **unproved proposition**, for an
arbitrary universe `u`. Neither this pair nor its structure supplies a metric or
proves the twisted-chamber theorem.

## The data and the assertion

Let `F` be a nonarchimedean local field and `K = inertiaFixedField F` its maximal
unramified extension. For a building datum `B` for `G_K` and its semilinear
apartment datum `A`, `A.MetricRealization` consists of:

- a `MetricSpace` on the original carrier `B.ReducedBuilding`;
- completeness of that metric;
- nonpositive curvature in the sense of KP Definition 1.1.8, expressed by
  `Langlands.Geometry.Metric.KP.IsNonpositivelyCurved`;
- isometry of the existing `G(K)` action on that carrier;
- isometry of each existing coefficient permutation `A.action sigma`, for
  `sigma` in `Aut(K/F)`.

The statement retains exactly the data of `UnramifiedTwistedChamberStatement`
through `hD`: `F`, a connected reductive `F`-group `G`, a supplied `F`-torus with
map `iT` whose scalar extension is maximal `K`-split, the supplied root-valuation
apartment datum `D`, centralizer datum `C`, compatibility `h6`, and Galois stability
`hD`. It asserts nonemptiness of `MetricRealization` for precisely
`UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD`, with `hGK` the
published connected-reductive scalar-extension proof. It asks for no cocycle,
extra building axiom, or prior metric. It asserts no existence of the supplied
algebraic or apartment data.

There is no chosen normalization, no comparison with another topology on the
building, and no continuity assertion about an action or the Galois group. The
metric induces its own topology. Completeness and curvature refer to that
metric. In particular, no local compactness or local finiteness is assumed for
the `K`-building, and no local-field instance for `K` is used.

## Derived source provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), with
the corrections and additions of 1 November 2024. The precise passages are:

- Section 4.2, Propositions 4.2.1 and 4.2.3 (printed pp.168–169; PDF pp.199–200):
  a compatible invariant Euclidean distance on apartments extends to a metric
  on the building, and the group action is isometric.
- Proposition 4.2.7 and Theorem 4.2.10 (printed pp.170–172; PDF pp.201–203):
  nonpositive curvature and completeness. The completeness argument covers
  buildings that are not locally finite.
- Proposition 7.6.3 and Remark 7.6.5 (printed pp.264–266; PDF pp.295–297):
  the root-valuation quotient construction and its building axioms, applied to
  the supplied integer-valued apartment data over `K`.
- Proposition 7.9.5 (printed p.276; PDF p.307) and Section 9.2.1
  (printed pp.324–325; PDF pp.355–356): coefficient automorphisms act on this
  building through the affine apartment construction.
- Corrections, PDF pp.1–2 and pp.27–29: the opening of Section 4.2 includes
  Axiom 4.1.6; the apartment distance in Proposition 4.2.1 must be invariant,
  and the apartment comparison must be interpreted with the corrected action.

This statement is a derived specialization of those results, rather than a
verbatim assertion of one source proposition. The coefficient-invariance clause
requires a compatible **choice** of Euclidean apartment metric: choose it
invariant under the Weyl group and the finite linear root permutations induced
by coefficient automorphisms. The translations already preserve it. The usual
apartment extension then makes both actions isometric. Proposition 7.9.5 alone
does not say that every arbitrary metric normalization is coefficient-invariant.
The existence assertion deliberately leaves the normalization free.

The formal prerequisites for applying these source results to the supplied
quotient, and the invariant metric construction itself, remain proof obligations
of `UnramifiedBuildingMetricStatement`. The supplied torus is not asserted to
contain a maximal `F`-split torus; no special-torus hypothesis is used or claimed.

## Intended use

For a finite-level cocycle, the existing finite-orbit helper provides one finite
orbit under the twisted action on the same carrier. With a realization as above,
that action is isometric and its orbit is bounded. The published
`Langlands.Geometry.Metric.KP.boundedActionFixedPoint` can then produce a common
twisted fixed point. This explains the interface; no fixed-point conclusion is
part of the present existence statement.
