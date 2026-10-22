# Integral matrix subgroups over topological rings

This module is derived internal infrastructure for standard finite adelic level
subgroups. It specializes existing Mathlib constructions; it does not quote a
new result from external literature.

For a commutative ring `R`, a subring `O`, and a finite index type `ι`,
`Langlands.GeneralLinearGroup.integralSubgroup ι O` is
`(O.matrix (n := ι)).toSubmonoid.units`. Mathlib's `Subring.matrix` is the
subring of matrices all of whose entries lie in `O`. Its `Submonoid.units`
consists of ambient matrix units whose value and inverse both belong to that
matrix subring.

Thus `mem_integralSubgroup` states precisely
`(∀ i j, g i j ∈ O) ∧ (∀ i j, g⁻¹ i j ∈ O)`. The inverse here is the inverse
in the general linear group. Requiring forward entries alone does not suffice:
an element of `O` can be a unit in `R` without its inverse belonging to `O`.
For example, the rank-one matrix with entry `2` is invertible over the rationals
and has integer entries, but its inverse has entry `1/2`.

No nonemptiness assumption is made on `ι`. The theorem
`integralSubgroup_of_isEmpty` proves that the subgroup is the whole group for an
empty index type, hence includes rank zero.

The ambient topology is Mathlib's units topology on the finite matrix ring. For
an open `O`, `isOpen_integralSubgroup` applies `IsOpen.matrix` and
`Submonoid.isOpen_units`. The latter takes the intersection of the inverse images
of the open matrix subring under the value and inverse-value maps.
`integralOpenSubgroup` bundles this actual subgroup and openness proof, and
`mem_integralOpenSubgroup` preserves the coordinate formula.

If `R` is a Hausdorff topological ring and `O` is compact,
`isCompact_integralSubgroup` applies `IsCompact.matrix` followed by
`Submonoid.units_isCompact`. This Mathlib theorem uses
`Units.isClosedEmbedding_embedProduct`: the units embed as pairs `(A,B)` with
`AB = 1` and `BA = 1`. These equations define a closed subset, by continuity of
matrix multiplication and closedness of the singleton identity. The two matrix
sets with entries in `O` are compact, so the inverse-pair subset is compact.
The multiplicative opposite in Mathlib's pair embedding changes the
multiplication bookkeeping, not its topology. The theorem
`isCompact_integralOpenSubgroup` gives the same result for the bundled subgroup.

These are general construction lemmas. They do not by themselves establish that
a number field's integral finite adeles are compact: that arithmetic input must
be supplied by the separate actual finite-adele subring construction.

Dependencies are Mathlib's `Data.Matrix.Basic`,
`Topology.Instances.Matrix`, `Topology.Algebra.Group.Matrix`,
`Topology.Algebra.Group.Units`, and `Topology.Algebra.OpenSubgroup`, through the
imports in the paired Lean file. No field topology is replaced and no local
completion or reciprocity object is introduced.
