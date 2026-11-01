# Rational restriction of actual finite full-domain covers

Author: Worker 36.

This module constructs rational restriction of finite covers by actual
full affinoid domains. The coefficient field is any complete ultrametric
normed field. The algebras retain finite positive-polyradius closed Tate
quotient presentations. No full-domain structural spectrum map is
assumed injective.

## Functorial intersection and its component pullbacks

For an ambient rational chart `d` and an actual domain inclusion
`f : U ⟶ V`, `Domain.rationalInterMap d f` constructs an inclusion from
`U.rationalInter d` to `V.rationalInter d`. It applies the full-test
intersection lift to the composite of the source's left projection
with `f`, and to the source's right projection to `d.toDomain`.
Thus its bounded restriction is constructed from the full affinoid-test
representation, rather than supplied as additional data.

The left and right projection equations follow from the full
representation's uniqueness of actual domain arrows.
`rationalInterMap_restriction_comp_left` exposes the left equation as an
equality of entire bounded algebra maps.
`Domain.rationalInterFunctor d` bundles the objects and arrows.
`rationalInterLeftNat` and `rationalInterRightNat` bundle their natural
projections to the identity functor and the constant rational domain.

`rationalInterMapPullbackCone d f` has point `U.rationalInter d`,
projection `U.rationalInterLeft d` to `U`, and projection
`rationalInterMap d f` to `V.rationalInter d`. The left naturality
equation makes it a cone over `f` and `V.rationalInterLeft d`.
`rationalInterMapPullbackConeIsLimit` constructs a lift from a competing
cone by combining its map to `U` with its map to `V.rationalInter d`
followed by the right projection to the rational domain. Full-test
uniqueness proves both projection equations and uniqueness of the lift.

`rationalInterMap_spectrum_left` proves commutativity of the same square
on actual quotient spectra by evaluating the equality of entire bounded
maps at every seminorm. `rationalInterMapSpectrumCone` stores this
concrete square. `rationalInterMapSpectrumConeIsLimit` proves its limit
property using the two already constructed spectrum pullbacks over
the ambient rational chart. The right-projection naturality and the
equation of `f` over the base identify the outer square with the source
rational spectrum pullback. Cancelling the target rational spectrum
pullback from this outer pullback proves the component square is a
topological pullback. No identification of either full-domain spectrum
with its locus is needed.

## Finite covers and chosen refinements

For any actual finite cover `c : Domain.FiniteCover U`,
`FiniteCover.rationalInter c d` keeps `c.size`, replaces each component
by `(c.obj i).rationalInter d`, and replaces its target inclusion by
`Domain.rationalInterMap d (c.map i)`. Each algebra is the actual rational
coefficient-pullback quotient over `(c.obj i).algebra`. Its locus is
exactly `(c.obj i).locus ∩ d.locus`.

Coverage follows pointwise: a point of `U.locus ∩ d.locus` lies in a
component of `c` and still satisfies the same rational inequalities.
The construction permits empty covers and empty loci.
`rationalInterComponentConeIsLimit` supplies the preceding actual
categorical pullback for every new component.
`rationalInterComponentSpectrumConeIsLimit` additionally supplies the
topological pullback of actual representing spectra for every component.

`Refinement.rationalInter` keeps a refinement's chosen component index
function and applies `Domain.rationalInterMap` to each of its actual
arrows. The projection lemmas expose these fields.
`FiniteCover.rationalInterFunctor U d` acts on the cover refinement
categories. Refinement extensionality reduces its identity and
composition laws to equality of the retained index functions.

## Concrete spectrum-cover triangles

`rationalInter_componentMap` compares the actual map from a new component
quotient spectrum to the old target locus along the two paths. One
path uses the new cover map followed by the target rational-locus
inclusion. The other uses the component's bounded rational quotient
projection followed by the original component spectrum-cover map.
The structural spectrum equation for that actual projection proves
equality at every seminorm.

`rationalInterSpectrumMap` maps the disjoint union of new rational
quotient spectra to the original component-spectrum disjoint union,
keeping the index and using the corresponding continuous spectrum
projection. Continuity follows componentwise.
`rationalInter_totalMap` assembles the component equations into the
commuting square for the actual total cover maps. These equations do
not identify a general full-domain spectrum with its locus.

## Original source and scope

The registered original is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p. 9, give
full affinoid-test representation, rational quotients and intersection
stability. Definition 2.2.7, printed/PDF p. 10, gives the actual
affinoid-domain embedding context.

The functors, naturality and finite-cover constructions are internal
derived consequences of the implemented rational intersection and full
representation property. They prove restriction of arbitrary finite
full-domain covers along a rational intersection. They do not establish
base change along arbitrary full domains, general spectrum injectivity,
Gerritzen–Grauert coverage, an unrestricted analytic atlas, Tate
acyclicity, or an etale or equivariant etale site.
