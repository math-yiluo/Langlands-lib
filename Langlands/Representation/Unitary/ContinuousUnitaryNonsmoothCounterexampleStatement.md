# Continuous unitary representations of t.d. groups need not be smooth

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, IV.2.2, opening paragraph, printed p. 97
(PDF p. 103). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`Langlands.Renard.CompactRepresentation.ContinuousUnitaryNonsmoothCounterexampleStatement`
asserts the existence of a Hausdorff locally compact totally disconnected group
with a continuous unitary representation on a complex Hilbert space that has a
vector with no open subgroup fixing it. It negates the universal implication
from continuity and inner-product preservation to `IsSmooth`. Both carriers
are in `Type`.

Continuity is strong continuity, expressed by continuity of every orbit
map in the Hilbert norm. Preservation of the inner product gives an
isometry for each group element, and its inverse acts by the inverse group
element. Strong continuity of this isometric action gives joint continuity.
