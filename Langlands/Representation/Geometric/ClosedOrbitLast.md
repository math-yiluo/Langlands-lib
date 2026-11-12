# Placing a specified closed orbit last

Author: Worker 124.

This internal supporting module constructs
`Langlands.Geometric.OrderedDoubleCosets.closedOrbitLast`. If an actual
`OrderedDoubleCosets P Q (m + 1)` ordering `s` has a specified closed orbit at
index `p`, the construction gives another actual ordering with that orbit last.
It keeps the same representatives and the relative order of all other orbits.
It changes the orbit cover before constructing any representation filtration;
it does not permute the grades of an existing extension.

`moveLastPermutation p` sends `Fin.last m` to `p` and each `i.castSucc` to
`p.succAbove i`. It is the equivalence through `Option (Fin m)` that deletes the
last position and reinserts it at `p`. Its two formulas are proved as simp
lemmas. Covers and disjointness transfer through that bijection.

For the open-initial-union condition, the full initial union remains the whole
space. At a proper threshold `k.castSucc`, the new initial union equals the old
initial union at threshold `p.castSucc.succAbove k`, minus the specified orbit.
The proof uses the strict order embedding `Fin.succAbove` to compare thresholds,
and disjointness to characterize the removed orbit. This difference is open
because the old initial union is open and the removed orbit is closed. Thus the
new ordering satisfies the full `OrderedDoubleCosets` interface, rather than
only a bijection of double-coset labels.

`closedOrbitLast_representative_last` records that its final representative is
exactly `s.representative p`.

`cosetOrbit_self_eq_singleton` proves, for any group and subgroup `P`, that a
representative `w ∈ P` has the singleton identity orbit
`cosetOrbit P P w = {Induction.quotientMap P 1}`. Membership of `w⁻¹q` in `P`
proves the forward quotient equality; choosing `q = w` gives the converse.
This equality needs no topology. When the left quotient is Hausdorff, the
singleton is closed and so supplies the input of `closedOrbitLast`. The module
does not derive Hausdorffness from closedness of `P`; that is the existing
left-quotient topology theorem used by consumers.

The ambient construction permits any topological group, any subgroup pair and
any positive finite orbit count. It asserts no existence or finiteness of an
orbit cover and no geometric lemma for representations. It has no root-system,
local-field, cuspidality, irreducibility or finite-length premise.

Provenance is internal: these are finite-ordering deductions from the published
`OrderedDoubleCosets` and `cosetOrbit` definitions in
[ClosedSubgroupDefinitions](ClosedSubgroupDefinitions.md). Dependencies are
`finSuccEquiv'`, its inverse formulas, `Fin.succAbove_lt_succAbove_iff`,
`Fin.castSucc_succAbove_castSucc`, `Fin.exists_succAbove_eq`, finite-index bounds,
`Set.disjoint_left`, `IsOpen.sdiff` and elementary quotient-group equality.
No external structural or representation-theoretic theorem is invoked.
This provides the endpoint-order refinement needed to apply the rank-one
short-exact-sequence assembly after the actual geometric grades have been
identified; normalized grade identification remains a separate obligation.
