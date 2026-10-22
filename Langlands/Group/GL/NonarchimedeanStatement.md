# Nonarchimedeanness of actual finite general linear groups

Author: Worker 6.

`Langlands.ValuativeGeneralLinearNonarchimedean` is a proposition definition.
It quantifies over a field `K` in an arbitrary universe, a valuative relation
on `K`, a topology on `K` that satisfies `IsValuativeTopology K`, and every
natural rank `n`. It asserts Mathlib's `NonarchimedeanGroup` for the actual
`Matrix.GeneralLinearGroup (Fin n) K`, using its existing matrix-unit topology.
It includes every positive rank; rank zero is harmless. It assumes neither
local compactness nor a nonarchimedean group structure on the matrix group.

This is an internal infrastructure target derived from the defining
neighborhood basis of a valuative field and the natural finite matrix-unit
topology. Its project purpose is to discharge the missing intrinsic hypothesis
of the already published generic compact-open subgroup theorem for actual
general linear groups. It is not an axiom, a proof, or a locally profinite
wrapper carrying that hypothesis. The more general theorem for totally
disconnected locally compact groups is not needed for this target.

For each supplied `PadicField.TopologicalData`, its `localField` certificate
provides `IsValuativeTopology`; thus a proof of this target can be specialized
to every supplied realization and to `canonicalTopologicalData`. The canonical
realization need not be an assumption of this generic statement. After that
specialization, the existing local compactness certificates in `GL/Padic.lean`
will permit application of the separately accepted compact-open theorem.

The target has no project definition dependencies. It uses the pinned Lean
4.34.0 environment and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, specifically the existing
`Topology.Algebra.Group.Matrix`,
`Topology.Algebra.ValuativeRel.ValuativeTopology`, and the imported
nonarchimedean-group interfaces. This internal statement has no external
literature attribution. Its proof must be submitted under an exact bound task,
pass the registered independent checker, and receive independent semantic
review and publication before it is used as accepted evidence.
