# Compact lifting for the actual unit filtration

Worker 92 implements the compact lifting argument and the complete entry theorem
`Langlands.LocalClassField.unitFiltrationTopologyTheorems.{u,v}`. Its exact type
is the published `Langlands.LocalClassField.UnitFiltrationTopologyTheorems.{u,v}`:
the structural laws in each of two independent carrier universes, together with
the compact lifting criterion between them. It quantifies every prime, both
fields and arbitrary supplied `TopologicalData`. Every natural filtration level,
including zero, is covered.

The module imports `Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof`
and reuses `unitFiltrationStructuralLaws` in universes `u` and `v`. Worker 102's
structural proof establishes compactness, closedness, antitonicity, separation
and the zeroth-level equality for the actual reduction-kernel image. It uses
compact local integer rings, closed ideals and compact integer units for
compactness, and Krull intersection for separation; its full implementation and
provenance are documented in [the structural proof](UnitFiltrationStructuralProof.md).
The existing statement pair and its imports are unchanged.

## Implemented lifting proof

`unitFiltrationCompactLifting_of_structural` isolates the compact argument with
the structural laws explicit. `unitFiltrationCompactLifting` discharges these
premises with the imported structural theorem. Thus the final criterion assumes
only the published preservation and one-level approximation hypotheses for a
continuous multiplicative homomorphism; compactness and separation are proved
facts, not additional hypotheses.

For a fixed starting level `n` and target element `y`, induction constructs a
source element in level `n` with error `y * (f x)⁻¹` in level `n + k`. At the
induction step, apply the one-level approximation to the current error and
multiply the resulting correction into `x`. Antitonicity keeps this product in
source level `n`.

Let `C k` be the set of these approximate preimages inside source level `n`.
Continuity of the homomorphism and of group operations makes each `C k` closed.
Each is nonempty by the induction, and target antitonicity makes the sequence
decreasing. The zeroth set is a closed subset of the compact source level.
Mathlib's compact intersection theorem supplies an element of every `C k`.
Target antitonicity places its error in every unshifted filtration level, and
target separation makes the error one. This gives the reverse subgroup
inclusion; preservation gives the forward inclusion. All steps include `n = 0`.

The two fields need no extension or algebra relation. The proof installs the
topologies and local-field instances from the supplied data, so continuity is
used for exactly the units topologies specified in the statement. Corrections
are multiplied in the commutative field-unit group, and the finite induction
uses precisely the stated one-level approximation at level `n + k`.
The final theorem assembles the structural theorem in both universes and this
lifting result without additional parameters.

## Source and derived scope

The underlying source is Jean-Pierre Serre, *Local Fields*, Greenberg translation,
GTM 67 (1979), Chapter V, Section 1, Lemma 2, printed p. 81 (PDF p. 88), registered
as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 92 read that original page for this implementation. Serre uses convergence
of successive corrections in complete filtered groups. Here a derived compact
specialization uses nested closed approximate-preimage sets instead. No arithmetic
norm theorem or local reciprocity result is used.

The structural part derives from the same source, Chapter II, Section 1,
printed pp. 26–28 (PDF pp. 34–36), and Chapter IV, Section 2, printed p. 66
(PDF p. 73), as documented in the imported proof. The exact Lean bundle and
the compact-intersection proof route are derived content rather than a claim
that Serre states this formulation verbatim.

The compact-intersection tool is
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` in
Mathlib's `Topology/Compactness/Compact.lean`. The environment is Lean 4.34.0
with Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
