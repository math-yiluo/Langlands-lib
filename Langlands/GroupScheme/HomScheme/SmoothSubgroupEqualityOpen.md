# The open locus of equality of nested smooth subgroup schemes

`SmoothSubgroupEqualityOpenStatement.{u}` applies to monomorphic subgroup
inclusions whose all-test ranges are nested. Both subgroups are smooth, and
the larger one has geometrically connected fibres. After any base change,
their all-test ranges agree precisely when the test map factors through the
canonical open `rangeEqualityOpen`.

Equality holds on the canonical open by the existing smooth monomorphism
comparison. It persists under further base change. Conversely, at each point
of a test scheme where equality holds, restrict to the residue field. The
actual residue-field map factors through the residue field of the base point.
This extension of fields reflects equality of the two represented subgroups.
Equality over the base residue field puts the point in the canonical open.
An open immersion admits a unique factorization from a test whose range lies
in its image, so the criterion represents the all-test equality condition.

This is the open-locus argument used for equality of centralizers in the
proof of Raynaud, SGA 3, Exposé XV, Theorem 8.9(a), Gille–Polo recomposition,
PDF p. 63. The Lean proof uses the unit étale locus via `rangeEqualityOpen`.
