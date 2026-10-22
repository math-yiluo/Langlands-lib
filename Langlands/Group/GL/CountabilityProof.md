# Countability of actual p-adic general linear groups and parabolics

Author: Worker 164.

This internal certificate module works with every prime `p`, every actual finite
extension `F : PadicField p`, every supplied compatible `F.TopologicalData T`,
every rank `n` (including zero), and every block shape `B` of that rank. The field
carrier universe is arbitrary. All conclusions use the exact topology supplied
by `T`; the declarations are explicit certificates, not global instances.

- The imported `generalLinearSecondCountableTopology` supplies second countability
  of the actual matrix unit group `GeneralLinear n F.Carrier`.
- `generalLinearSigmaCompactSpace` proves sigma compactness of that group.
- `parabolicSecondCountableTopology` proves second countability of the actual
  subgroup `B.parabolic F.Carrier` with its induced topology.
- `parabolicSigmaCompactSpace` proves sigma compactness of that subgroup.

## Construction and provenance

The published
`Langlands.PadicField.TopologicalData.generalLinearSecondCountableTopology`
from `Langlands.Representation.Smooth.SmallRealizationProof` already establishes
second countability of the actual general linear group with the supplied topology.
This module imports and reuses that certificate. Its proof, documented in
[SmallRealizationProof.md](../../Representation/Smooth/SmallRealizationProof.md),
uses field second countability, finite matrix products, the multiplicative
opposite homeomorphism, and the topology induced by the unit-group embedding.
Here subtype second countability gives the parabolic certificate.
For both groups, the published topological-group and local-compactness
certificates, together with second countability and hence separability, supply
Mathlib's sigma-compactness instance for separable locally compact topological
groups.

These are internal consequences of published topology constructions and Mathlib
instances. They introduce no additional field realization, countability
hypothesis, or representation-theoretic assertion. They supply topology
prerequisites for finite-orbit ordering; they do not prove an orbit ordering or
the geometric lemma.

The closing theorem `Langlands.PadicField.matrixGroupCountability` has exactly
`Langlands.PadicField.MatrixGroupCountabilityTheorem` as its complete type. It
introduces the prime, actual field, supplied topology and rank and groups the
four certificates into the required conjunctions. The statement and its imports
are unchanged.
