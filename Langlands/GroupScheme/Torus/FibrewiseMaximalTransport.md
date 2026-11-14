# Transport of fibrewise maximal tori

This module provides internal transport lemmas for the actual inclusions used
in the proof of étale-local maximal-torus existence. Its provenance is the
published residue-field factorization, field-extension reflection of maximality,
and base-change coherence lemmas in the Library; it introduces no new
geometric existence input.

`isMaximalTorus_residueFibre_of_fieldPoint` applies to a closed inclusion into
any group scheme. It factors a supplied field point through the residue field
of its image, transports maximality to the successive pullbacks, and reflects
it along the resulting field extension using `IsMaximalTorus.of_baseChange`.
It requires neither smoothness nor affineness.

`IsFibrewiseMaximalTorus.baseChange` requires the ambient group to be smooth
and affine. For each residue point of the new base, the composite field point
has maximal pullback by `IsFibrewiseMaximalTorus.fieldPoint`; the base-change
comparison then gives the required maximality on the new residue fibre.

`IsFibrewiseMaximalTorus.comp_iso` transports each residue-fibre inclusion
through the pullback of the supplied ambient isomorphism. It needs no
smoothness or affineness hypothesis.
