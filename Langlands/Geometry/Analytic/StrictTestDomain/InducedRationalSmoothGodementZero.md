# Degree-zero proper rational smooth Godement maps

This internal extension uses the existing actual induced rational spectra,
their full smooth coefficient sheaves, compact Godement complexes and canonical
degree-zero identifications. The field is complete, normed and ultrametric; the
strict affinoid algebra is presented. The field, topological group, coefficient
ring, spaces and coefficient carriers share universe `u`. The section and
cohomology comparisons require `HasStableNeighbourhoods` on each induced
spectrum. The original invariant compact-function map and its laws do not
require this condition. Each pullback has an explicit properness hypothesis
on its actual induced map.

`invariantCompactSupportPullbackNatTrans` applies whole-group invariants to the
existing proper pullback of full compact functions. Its underlying function is
precomposition with the constructed balanced quotient spectrum map. Its
identity and contravariant composition equations follow by applying the
invariants functor to the existing equations.

The two `coefficient…SectionsNatTrans_toFunctions` equations compare the actual
full-coefficient compact-section pullback with the original compact-function
pullback, including its invariant restriction. Extensionality reduces them to
the same precomposition formula under the existing section/function
isomorphisms.

`godementCohomologyPullbackNatTrans_zero_toFunctions` applies the generic
degree-zero spatial square from `SmoothGodement.ZeroSpatial` and the section
comparison. It identifies degree zero of the actual all-degree chain-induced
map with proper compact-function pullback under the existing canonical
isomorphisms. Cancellation proves equality with the previously defined
`godementZeroPullback`; the compact map is not redefined here.

`godementInvariantZeroPullback` and `invariantCompactDerivedZeroPullback`
transport the original invariant compact-function map through the already
constructed degree-zero Godement and sheaf-derived isomorphisms. They are
natural transformations in every original smooth coefficient object and
intertwiner. Their equations to functions, strict identity and composition,
and compatibility with `godementInvariantDerivedZeroIso` follow by cancelling
inverse isomorphisms and using the compact-function equations.
Their pointwise application equations evaluate those transformation equalities
at a coefficient object, a cohomology class and a point. They identify the
resulting original invariant functions with precomposition by the actual
induced map.

`godementInvariantCohomologyPullbackNatTrans_zero_toFunctions` gives the same
square for the actual all-degree module homology map after termwise invariants.
Cancellation proves equality with `godementInvariantZeroPullback`.
Invariants are taken before homology throughout; no exactness of invariants or
commutation with higher compact cohomology is used.

The provenance is internal composition of the existing proper compact-function,
full coefficient sheaf, spatial Godement and canonical degree-zero
constructions. The results concern ordinary-open locally constant smooth
coefficient sheaves on the actual induced spectra. They assert no higher
sheaf-derived pullback, Godement acyclicity or resolution exactness, analytic
etale realization, Shimura uniformization or Harris compatibility. Stable
neighbourhoods and properness of arbitrary transport data remain explicit
inputs.
