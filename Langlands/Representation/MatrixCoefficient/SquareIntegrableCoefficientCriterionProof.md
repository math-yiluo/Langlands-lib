# One square-integrable coefficient suffices

Author: Worker 144. This module proves the published proposition
`Langlands.Renard.CompactRepresentation.SquareIntegrableCoefficientCriterionStatement`
without changing its statement, universes, or hypotheses.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.3.2 Remark, printed page 100 / PDF page 106,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard leaves the proof of this remark to the reader. The proof here supplies
two successive orbit-spanning arguments under the published admissibility
hypothesis.

For a fixed smooth functional, the vectors with square-integrable coefficient
norm form a complex submodule. The triangle inequality, continuity of the
descended norm for smooth vectors, and domination in `MemLp` prove closure
under addition. The norm identity for scalar multiplication proves closure
under scalars. Right translation on the actual quotient by the center sends
the coefficient of a vector to that of its translate. Continuity of each
translation and right invariance of the given measure make this operation
measure preserving. The nonzero coefficient implies that the original vector
is nonzero. Its orbit spans by irreducibility, so every vector has a
square-integrable coefficient for the original functional.

Next, the smooth functionals whose coefficients for every vector are
square-integrable form a complex submodule by the same norm estimates.
The smooth contragredient acts by inverse left translation, which preserves
square-integrability by left invariance of the given Haar measure. The
original functional is nonzero, and its orbit spans the smooth dual.
Here `Topology.isLocallyProfinite_of_mathlib` and the published
`Topology.LocallyProfiniteProof.vanDantzig` derive compact-open cofinality
from the supplied locally compact, Hausdorff, totally disconnected group
topology. The published `SmoothRep.isIrreducible_contragredient_iff` then
gives irreducibility of that dual under the supplied admissibility. Thus every smooth matrix coefficient is square-integrable.
Together with the supplied admissibility and unitary central character,
this is exactly `IsSquareIntegrableModCenter`.

The translations are shown measurable individually using continuity. No
second countability or joint measurable-multiplication hypothesis is added.
The proof uses no tensor-product irreducibility result and no conditional
representation-theoretic premise.

The final theorem is `squareIntegrableCoefficientCriterion` in namespace
`Langlands.Renard.CompactRepresentation`, with independent universes `u`
for the group and `v` for the representation carrier. The orbit-spanning
input is `Langlands.span_range_orbit_eq_top`; measurability comes from
`UnitaryCentralCharacter.aestronglyMeasurable_coefficientNorm`. All inputs
are imported from the published Library by module name.
