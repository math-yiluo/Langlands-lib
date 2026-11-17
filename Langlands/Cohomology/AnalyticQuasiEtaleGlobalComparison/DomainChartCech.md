# Actual compact lifted Čech presentations for domain-chart covers

Work over a complete ultrametric normed field with equal space and chart
universes. Fix an actual finite compact domain-chart cover `C` of a quasi-étale
site object `U`, an action lift `l` on `U → X`, and continuous actions `σ i` of the
same open subgroup on the selected source objects. Assume the actual chart
arrows commute with these actions and the action of `l`.

`chartSourceActionLift` proves that these source actions are lifts of the base
action. Its equivariance equation is obtained by composing the chart-arrow
equivariance with the target lift's structure map. `chartLiftBasisIndex` retains
these actual lifts and the stored compactness of each chart source.
`compactLiftBasisCover` reindexes the chart family using `Fintype.equivFin`.
Surjective reindexing preserves the actual generated covering sieve, so this
is a finite cover with sources in `CompactLiftBasis`.

Assume also that the underlying space of `U` is Hausdorff. For every tuple of
`n + 1` selected indices, `tupleLiftBasisIndex` uses the actual finite domain
intersection `wideObj`. Its compact Hausdorff property is the proved finite
intersection theorem, and its lift is the actual continuous restriction
constructed in `ContinuousDomainWidePullbacks`. This retains the original
common subgroup; it does not choose an unrelated lift for each tuple.

`domainChartCechPresentation` applies `cechPresentationOfCones` to the actual
intersection cones, their proved universal properties against all quasi-étale
test objects, and identity isomorphisms of the chosen basis objects. It thereby
constructs a finite representable coproduct presentation in every degree of
the actual cover's presheaf Čech nerve. No nerve presentation or existence of
limiting cones is an additional hypothesis.

This is an internal combination of the published finite-chart covering,
domain-intersection, continuous action restriction, compact lifted basis and
finite Čech presentation APIs. The hypotheses concern compatible actions on a
domain-chart cover. They do not establish that such covers refine every
quasi-étale cover; in particular, the module does not provide presentations for
arbitrary compatible quasi-étale covers or prove the global comparison theorem.
