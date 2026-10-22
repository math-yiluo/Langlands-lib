# Proof of admissibility invariance under character twists

Worker 4 authored this internal derived proof. Worker 68 checked the draft
against the published target and prepared the contribution.
`fixedVectors_twist_eq_of_le_ker` proves equality of the two submodules
by extensionality. For an element of the subgroup, the character value
is the unit `1`, so the twisted fixing equation reduces to the original
fixing equation. This helper needs neither topology nor Noetherian
coefficients and remains in the proof that uses it.

For `isAdmissible_twist_iff`, let `L` be the open character kernel and
`S` the set of open subgroups contained in that kernel. For every open
subgroup `K`, its intersection `K ⊓ L` belongs to `S` and is contained
in `K`, proving downward cofinality. Apply the accepted
`isAdmissible_iff_of_cofinal` to both representations. Their smoothness
conditions are equivalent by the accepted `isSmooth_twist_iff`. On
each member of `S`, the first helper identifies the fixed submodules,
and `LinearEquiv.ofEq` gives their identity linear equivalence.
`Module.Finite.equiv_iff` transports finite generation along that
equivalence in both directions.

The closing theorem `twistAdmissibilityCompatibility` proves the whole
`Langlands.TwistAdmissibilityCompatibility` proposition. It introduces
the topology and Noetherian instances only for the second conjunct.
There are three independent carrier universes, and no hypotheses
beyond those in the paired statement. The proof uses cofinality
directly and does not assume finite generation of arbitrary submodules
over a non-Noetherian ring.

## Dependencies and status

The target is the Library declaration
`Langlands.TwistAdmissibilityCompatibility` in
`Langlands.Representation.Twist.AdmissibilityStatement`.
The published proof imports are:

- `Langlands.Representation.Twist.SmoothProof`.
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`.

The scalar-twist and smooth-representation definitions come from
`Langlands.Representation.Twist.Definitions` and
`Langlands.Representation.Smooth.Definitions`. The proof imports these
published results without changing the target or duplicating their proofs.

This is an internal derived proof by the cofinality argument described above.
Compilation and exact-type development checks do not establish independent
proof acceptance; the contribution requires semantic review and publication.
No project axiom or external mathematical theorem is assumed.
