# Renard III.3.1: original coinvariant sheaf, fibres and distributions

These are unproved closed proposition targets for David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, III.3.1, printed pp.83–84 / PDF pp.89–90: the construction's
compact-section identification, the Proposition identifying the fibre of
`F′` and the following distribution Corollary. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original pages were read directly.

All declarations have prefix
`Langlands.Sheaf.Renard.CoinvariantStatements`. None is a theorem proof or
an assumed comparison certificate.

## Original data and scope

Every target quantifies over an actual topological group `G : Type` with
explicit `IsLocallyProfinite G`, spaces `X Y : Type` with explicit
`IsLocallyProfinite` predicates, and a jointly continuous action on `X`.
Hausdorffness, compact-open neighbourhood bases and actual supplied
topologies and actions are retained. The map `q : C(X,Y)` is the original
continuous map, with actual invariance `q(g • x)=q x`. Coefficients,
original section carriers, original stalks and quotient carriers are
universe zero, as in the actual inverse-image interfaces. No smoothness,
properness, surjectivity, countability, transitivity or finite-dimensionality
assumption is added. These assertions precede the smooth category and
transitive-space discussion in III.3.2.

## The canonical compact-section comparison

`CompactComparisonStatement` requires that every component of the already
constructed natural transformation
`CoinvariantSheaf.compactComparison hX q hq hY` be an isomorphism of the
original nondegenerate target-test modules.

Its source is the literal original representation-coinvariant quotient of
all original compact sections, with the nondegenerate target-test action
from `CoinvariantTestModule`. The canonical-complex action has exactly the
original compact-section operators and scalars. Its target is all actual
compact sections of the actual `CoinvariantSheaf.functor` value `F′`.
The map is the published original-module comparison: a quotient vector
is sent to the original global compatible family of its compact-open
projections. Thus the target asserts invertibility of a particular
constructed map; it does not assume an isomorphism when defining `F′`.

## The fibre Proposition

`FibreCoinvariantStatement` requires a natural isomorphism of functors in
the original action sheaf `F`, for every actual point `y : Y`.

The left functor is `CoinvariantSheaf.functor` followed by the ordinary
sheaf forgetful functor and Mathlib's original neighbourhood-colimit
`TopCat.Presheaf.stalkFunctor` at `y`. Its object is the literal stalk
`F′_y` of the actual reconstructed sheaf.

The right functor is exactly `InvariantFibres.coinvariants q hq y`.
Its fibre is the actual subtype `{x : X // q x=y}` with its original
subspace topology and inherited original group action. Restriction is
the actual equivariant sheaf inverse image along its inclusion; the
published comparison identifies its ordinary sheaf with the ordinary
inverse image. The representation takes all original compact sections
of that actual restriction, and the quotient is the existing
`Representation.Coinvariants`. The functor maps are the original sheaf,
compact-section and coinvariant maps. Thus the output is precisely a
natural complex-linear identification

```text
F′_y ≅ (F|_(q⁻¹{y}))_c(q⁻¹{y})_G.
```

The natural isomorphism is a conclusion. This target specifies its exact
original endpoints and naturality in `F`, without asserting a particular
map on representatives. The source proof's compact restriction
surjectivity, kernel span and successive quotient identifications remain
proof obligations; none is silently supplied as input data.

## The distribution Corollary

`NoInvariantDistributionsStatement` says that if, for every actual fibre,
every invariant algebraic distribution on the compact sections of the
actual restricted sheaf is zero, then every invariant algebraic
distribution on the original ambient compact sections is zero.
`Distribution` and `IsInvariantDistribution` are exactly the published
algebraic dual and invariance predicates, with no topology on the dual.
It does not restrict to smooth dual vectors. Empty fibres are included.

The printed proof invokes restriction of an arbitrary distribution to a
point stalk. No such general restriction is assumed or asserted here.
A proof can instead use the Proposition: zero duals of fibre coinvariants
force those vector spaces to vanish, hence the original stalks of `F′`
vanish; sheaf separation and the canonical compact comparison then give
zero global coinvariant dual. This is a proof route, not a proved
reduction in this module.

`Statements` conjoins the three targets while retaining their full names
for separate focused proof tasks. The actual sheaf/module and homogeneous
category equivalences are separate declarations.
