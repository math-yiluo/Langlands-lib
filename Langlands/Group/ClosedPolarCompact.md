# Maximal compact subgroups from closed polar matrix realizations

Author: Worker 1571.

This internal auxiliary construction uses the unitary inverse-image subgroup
and positive-semidefinite rigidity from `Langlands.Group.MatrixPolarCompact`.
The scalar `𝕜 : Type u` is any `RCLike` field, the rank is any natural number,
and the original group `A : Type v` has an independent universe and its supplied
topology. No compatibility of the topology with group operations is needed for
these two declarations.

`isCompact_unitarySubgroup` assumes that the representation `ρ` is a closed
topological embedding into the ordinary matrix-units topology. Mathlib's actual
unitary-to-units homomorphism is continuous: both its value and inverse value
are continuous on the unitary group. The standard unitary matrix group is
compact by `Langlands.Global.isCompact_unitaryMatrix`, which also supplies its
`CompactSpace` instance. The image in matrix units is therefore compact, and
a closed embedding has compact inverse images. That inverse image is exactly
`unitarySubgroup ρ`.

`maximalCompactOfClosedPolar` constructs a subgroup together with compactness
and unrestricted compact-overgroup maximality. Its subgroup is
`unitarySubgroup ρ`. Its arguments are a closed topological embedding `ρ` and
a factorization of every original group element into an original unitary
factor and an original factor whose matrix is positive semidefinite. The
maximality law applies `compact_overgroup_eq` to these arguments.

This is an elementary internal construction, derived from the cited Library
and Mathlib compactness facts and the earlier matrix rigidity argument. It does
not prove that an actual reductive group has a realization with these polar
factors. It also asserts no parabolic coverage. Those obligations, with the
actual completion-point topology, must be established separately to prove
`Langlands.Global.InfinitePlaceGroupPoints.ParabolicIwasawaStatement`.
