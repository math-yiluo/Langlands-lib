# Renard IV.2.2: the endomorphism criterion

Author: Worker 89.

This module proves the exact published proposition
`Langlands.Renard.CompactRepresentation.UnitaryAdmissibleEndomorphismStatement`
as `unitaryAdmissibleEndomorphism`, with independent group and carrier universes.
The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, IV.2.2 Corollary (i), printed p.98 /
PDF p.104. Source ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implemented argument uses published results. Van Dantzig's theorem and the
conversion from a locally compact Hausdorff totally disconnected space to a
locally profinite space produce compact-open cofinality. Admissibility and
unitarizability then give algebraic semisimplicity by
`admissibleUnitarySemisimplicity`.

If the endomorphism space has finrank one, the carrier is nontrivial: a
subsingleton carrier would have only the zero intertwiner and finrank zero.
The rank-one identity follows from Mathlib's exact equivalence between rank
one and finrank one, so infinite-dimensional finrank zero causes no issue.
The published `isIrreducible_of_semisimple_rank_endomorphism_le_one` now proves
irreducibility. That result uses the projection onto a proper semisimple
summand to produce a nonscalar endomorphism in the reducible case, as in
Renard's proof.

Conversely, admissible Schur identifies the endomorphism space of an
irreducible representation with the scalar field. Equality of finranks under
this linear equivalence gives finrank one. All hypotheses of the published
target, including first countability, are retained; first countability is not
needed by these stronger published inputs. No premise is added.
