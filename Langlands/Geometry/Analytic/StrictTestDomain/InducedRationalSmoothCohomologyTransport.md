# Proper transport of degree-zero smooth cohomology

This internal construction equips both actual degree-zero cohomology objects
on induced rational spectra with proper transport pullback. It uses their
proved natural identifications with full compactly supported locally constant
functions. The valued field, group, coefficient ring and coefficient carriers
share universe `u`. The field is complete and nonarchimedean, the ring is
commutative, and the group is a topological group. Stable neighborhoods remain
explicit on each induced spectrum involved.

For a morphism `f : X` to `Y` of open-subgroup transport objects, the map
`f.inducedMap` is the existing constructed continuous equivariant map of actual
balanced quotient spectra. Both `godementZeroPullback` and
`compactDerivedZeroPullback` require a proof that this map is proper.
They first identify a degree-zero vector on `Y` with its actual compact
function, apply the existing full-group equivariant compact-support pullback,
and use the inverse degree-zero identification on `X`. Thus the resulting
maps are natural transformations in all smooth coefficient intertwiners and
are morphisms of smooth representations.

The two `toFunctions` equations and their pointwise application formulas prove
that the resulting compact function is precomposition with `f.inducedMap`.
The identity and composition laws follow from the existing proper compact
function pullback laws and the inverse laws of the degree-zero identifications.
`godementDerivedZeroIso_pullback` proves that the original Godement/derived
comparison commutes with these pullbacks.

The provenance is internal conjugation of the existing actual proper
compact-function maps by the already constructed degree-zero natural
isomorphisms. These are definitions of the degree-zero maps, not a claim that a
higher derived pullback or a map on Godement resolutions was constructed.
The underlying geometry is the actual induced rational spectrum on ordinary
opens. Higher cohomological functoriality, analytic or etale comparisons,
acyclicity and arithmetic specialization remain separate obligations.
