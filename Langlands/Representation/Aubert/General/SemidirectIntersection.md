# The intersection in a semidirect decomposition

For subgroups `P`, `M`, and `U` of any group, a supplied
`IsSemidirectDecomposition P M U` implies that an element of both `M` and `U` is `1`.
The proof compares its Levi projection with the identity on `M` and its trivial value
on `U`. No topology is required.

The theorem `IsSemidirectDecomposition.eq_one_of_mem_of_mem` in
`Langlands.Aubert.General.RepresentedParabolic` is moved unchanged from
`Intertwining/PQBoundaryVanishingCompactSupportProof` and shared with
`Intertwining/InnerLeviBoundaryTransfer`.
