# Topology of actual rational-point discrete-series orbits

Author: Worker 200.

This derived adapter specializes `DiscreteSeriesOrbitTopology` to the shared
actual rational-point group and all rational norm characters. Its source
motivation is Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), III.7, printed p.273 (PDF p.39),
and VI.1, printed pp.295–296 (PDF pp.61–62), registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
III.7 parameterizes a discrete-series orbit by unitary unramified characters
modulo the full stabilizer. VI.1 uses character parameters for coefficient
families. This unit supplies actual-point topological consequences of the
existing parameterization; it defines no smooth structure or coefficient
family.

## Actual objects and topology

The field `F : Type u` has the existing `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances, with no
characteristic restriction. The shared `GroupScheme G` is affine and locally
of finite type. Its rational points carry exactly
`rationalPointTopology F G.X`; `rationalPoints_nonarchimedeanGroup` supplies
the previously proved open-subgroup identity basis in that topology.
The representation universe `uV` is independent of `u`.

Let `s : T.toGrp ⟶ G` be an actual morphism from a commutative group scheme,
with `hs : GroupScheme.IsCentral s`. The central subgroup is the actual
point-map range `s(T(F))`. Its normality is derived from `hs.range_le_center`
before the dependent Haar-measure and class binders. Give the actual quotient
by this subgroup a measurable space and a Haar measure `mu`.
The discrete-series classes, unitary twist action, stabilizer and orbit are
the existing canonical objects. The positive-character family is precisely
`fun psi => (rationalNormCharacters G psi).toMul`, using every rational
algebraic character and the actual residue-normalized field absolute value.
The orbit carries the existing stabilizer-quotient topology; no topology on
the whole smooth dual is assumed.

## Compactness and separation

`compactSpace_rationalDiscreteSeriesOrbit` installs the published
`compactSpace_rationalUnitaryUnramifiedCharacters` and applies the generic
orbit compactness theorem. Thus this actual orbit is compact without
connectedness, reductivity, finite rank, finite stabilizer or an actual-image
finite-index premise. No affineness or finite type of `T` is required here.

`t2Space_rationalDiscreteSeriesOrbit` additionally assumes `T` affine and
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.
The published `finite_rationalDiscreteSeriesStabilizer` supplies the finite
actual unitary stabilizer, which the generic orbit theorem uses as a closed
subgroup of the Hausdorff character group. Its quotient, and hence the orbit,
is Hausdorff. Together the two results give a compact Hausdorff orbit under
the displayed finite-index premise.

The finite-index input is about the actual composite point-map/valuation
range. Its general reductive realization remains a separate proof obligation.
The underlying quotient argument is the deduction of finiteness from actual
split-center valuation-image finite index in Renard, *Représentations des
groupes réductifs p-adiques*, 9 July 2026 edition, V.2.6, printed p.108
(PDF p.114), source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This adapter uses that conditional chain through `RationalTwistStabilizer`.
It does not prove or reclassify the preceding in-book finite-index lemma.

## Existing finite coordinates and the actual orbit map

If `hG : GroupScheme.IsConnectedReductive G`, the published
`rationalCanonicalUnitaryUnramifiedCharacterCoordinates` identifies the
actual unitary unramified character group with
`Fin (rationalImageRank G) → Circle` as topological groups.
`rationalDiscreteSeriesOrbitCoordinateMap` first reconstructs a character
using the inverse of that same coordinate map, then applies the actual
unitary twisting map into the orbit. Its `_val` theorem identifies the
underlying class with that reconstructed character acting on `omega`.
The previously proved Laurent evaluation formula for this character remains
unchanged; this unit chooses no additional basis or coordinates.

`isOpenQuotientMap_rationalDiscreteSeriesOrbitCoordinateMap` composes the
homeomorphism given by inverse character coordinates with the existing open
quotient orbit map. It proves continuity, openness, surjectivity and the
quotient property for this actual parameterization. No finite-index premise
is needed for that property. The already constructed
`discreteSeriesOrbitBaseChange` applies to these same actual data and proves
base-point independence through an identity-on-classes homeomorphism.

## Scope

The intended source application takes `s` to be the actual split-component
inclusion. This unit does not construct that inclusion or prove its actual
valuation-image finite index, nor identify `rationalImageRank G` with the
split-center dimension. It constructs no manifold, coefficient family, orbit
measure, formal degree or spectral transform. It asserts no finiteness of a
set of representation classes or orbits, and no wave-packet, inversion or
Plancherel result. All compactness and quotient-map conclusions use actual
objects in the canonical point and compact-open character topologies.

Local instances use explicit module-specific names to prevent generated-name
collisions under joint imports. Their types, bodies and local scope are
unchanged.
