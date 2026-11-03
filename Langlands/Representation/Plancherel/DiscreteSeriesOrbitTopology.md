# Quotient topology on discrete-series twist orbits

This is a derived construction from the actual twisting action in
`DiscreteSeriesOrbits`. The source is J.-L. Waldspurger, *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)* (2003),
III.7, printed p.273 (PDF p.39), and VI.1, printed pp.295–296
(PDF pp.61–62), source ID `waldspurger-2003-plancherel`.

III.7 parameterizes an orbit by the unitary unramified character group modulo
the stabilizer. VI.1 uses this parameterization to define smooth coefficient
families. Here we supply the quotient topology underlying that construction
and prove independence of the base representation. This module constructs no
smooth structure or coefficient family.

## Objects and hypotheses

The group is a topological `NonarchimedeanGroup`; its universe and the
representation-carrier universe are independent. The normal subgroup `A`,
its centrality proof `hA`, the quotient measurable space, its Haar measure
`mu`, and a family of positive characters `nu` remain explicit.
`DiscreteSeriesClass A hA mu` is the existing subtype of canonical irreducible
admissible smooth representation classes square integrable on that quotient.
The action and stabilizer are the existing unitary character twisting action
and its actual stabilizer.

The unitary character group has its existing compact-open subspace topology.
`discreteSeriesOrbitTopologicalSpace` gives the actual orbit subset a topology
by transporting the quotient topology through `discreteSeriesOrbitEquiv`.
This is a topology on each orbit subtype; no topology on the entire smooth
dual is assumed or defined.

`discreteSeriesOrbitHomeomorph` upgrades that same equivalence to a
homeomorphism. Its formula on the class of a character is the actual twisted
representation class, as `discreteSeriesOrbitHomeomorph_mk` states.
`discreteSeriesOrbitMap` is the resulting map from a character to its twist
in the orbit; `discreteSeriesOrbitMap_val` records that formula.
`isOpenQuotientMap_discreteSeriesOrbitMap` composes the open quotient
projection with this homeomorphism. The continuity corollary is
`continuous_discreteSeriesOrbitMap`.

## Compactness, separation and base point

`compactSpace_discreteSeriesOrbit` transfers compactness of the character
group to its quotient and then to the orbit. It explicitly requires a
`CompactSpace` instance for the unitary unramified character group. For actual
affine locally finite type rational points that premise is already proved by
`compactSpace_rationalUnitaryUnramifiedCharacters`.

`t2Space_discreteSeriesOrbit` explicitly requires finiteness of the actual
unitary stabilizer. A finite subgroup of this Hausdorff character group is
closed. Since the character group is commutative, its quotient by that subgroup
is a topological group and is Hausdorff; the orbit homeomorphism transfers
this property. No finiteness assertion for a family of representations or a
set of orbits follows.

`discreteSeriesOrbitBaseChange omega chi` is a homeomorphism from the orbit
based at `chi • omega` to the orbit based at `omega`. Its underlying map and
inverse are identity maps on representation classes, as the two `_val`
lemmas state. To prove continuity, descend along the open quotient orbit
maps. On character parameters the forward identity is translation by `chi`,
and its inverse is translation by `chi⁻¹`; both are continuous. The group
action laws identify these compositions with the same underlying classes.
Thus the quotient orbit topology is independent of the chosen base class
within an orbit.

## Scope

For the source application the norm family must be all rational
absolute-value characters and `A` the actual split-center point image.
This module does not construct that split component, discharge the actual
valuation-image finite-index theorem, identify the full stabilizer with the
unitary stabilizer, or prove compactness of a generic supplied character group.
The corresponding existing actual-point results remain separate inputs to
specializations. Lie-group or manifold structures, smooth families, measures
with the VI.3 normalization, formal degrees and all spectral finiteness,
wave-packet and Plancherel assertions remain separate obligations.
