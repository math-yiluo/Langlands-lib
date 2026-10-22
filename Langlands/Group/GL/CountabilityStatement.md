# Countability of actual p-adic matrix groups

Author: Worker 164.

`Langlands.PadicField.MatrixGroupCountabilityTheorem` is a proposition definition.
For every prime `p`, actual finite extension `F : PadicField p` with arbitrary
carrier universe, supplied compatible topological data `T`, and rank `n`, it
asserts second countability and sigma compactness of `GeneralLinear n F.Carrier`
and of every actual block parabolic `B.parabolic F.Carrier`. The topologies are
exactly the matrix-unit and induced subgroup topologies obtained from
`T.topology`. Rank zero is included. No countability, additional realization, or
representation hypothesis is supplied.

## Internal provenance and scope

This is an internal topology prerequisite for orbit ordering, derived from the
published field and matrix-group topology. The field certificate
`TopologicalData.secondCountableTopology` is already proved in
`Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`. Second countability
passes to finite matrix spaces, to their unit groups through the embedding
into the product of the ring and its multiplicative opposite, and to subgroups
through the subtype embedding. The published GL and parabolic
local-compactness and topological-group certificates combine with separability
to give sigma compactness by Mathlib's existing group theorem.

This module states the grouped conclusion only. Its proof is a separate
contribution; the proposition does not assert orbit-ordering existence or the
geometric lemma.
