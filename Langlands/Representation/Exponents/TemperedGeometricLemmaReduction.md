# Conditional assembly of the tempered geometric lemma

Authors: Worker 1725 and Worker 1221. This internal reduction connects the
supplied-filtration adapter `LeviUnitaryFiltration` with the selected-piece
comparison `TemperedGeometricPiece`. It is derived infrastructure for Renard
2026, VII.2.5 (printed p.230 / PDF p.236), and does not prove the unconditional
`TemperedGeometricLemmaStatement`.

`TemperedGeometricLemmaReductionStatement` states an implication from the
following published proposition targets to the exact published
`TemperedGeometricLemmaStatement.{u, v}`:

- `RepresentedGeometricLemmaStatement.{u, v}`;
- `ParabolicRootPresentationExistenceStatement.{u}`;
- `ArbitraryParabolicQuotientCompactStatement.{u}`;
- `ArbitraryParabolicJacquetAdmissibilityStatement.{u, v}`;
- `ArbitraryParabolicJacquetAdmissibilityStatement.{u, max u v}`.

The two Jacquet-admissibility hypotheses serve distinct carrier universes:
the original inducing representation has carrier universe `v`, while one
normalized induction has carrier universe `max u v`. The field universe `u`
and carrier universe `v` remain independent.

`temperedGeometricLemma_of_structuralInputs` proves this implication. It
introduces the exact target's field, topology, connected reductive group,
actual parabolic triples, arbitrary split component of `L`, and tempered
representation. It installs the published Levi-point topologies and their
derived local compactness and nonarchimedean group instances.

The supplied represented geometric lemma provides a finite enumeration of
the actual double cosets, representatives, intersection data `D`, and an
`IsGluedFrom` witness. Presentation existence supplies a root presentation of
`Q` for the specified split component of `L`. Temperedness supplies
admissibility of the original representation. Quotient compactness and the
published induction-admissibility theorem give admissibility of its actual
normalized induction; Jacquet admissibility at `max u v` and transport along
`leviPointsEquiv` then give admissibility of the Jacquet-induction value.

For every family of split components of the Levis `(D i).M'`, the supplied
gluing and this ambient admissibility yield the actual unitary Jacquet
filtration through
`exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom`. The same number
of grades and the same permutation are retained, including repeated steps
and zero grades. For each grade, Jacquet admissibility at universe `v`
supplies the hypothesis of
`GeometricLemmaIntersectionDatum.nonempty_selectedWeightPart_pieceFunctor_equiv`.
Composing its equivalence with the selected-grade equivalence gives exactly
the target `unitaryPieceRep` for that grade.

The piece comparison uses direct exponent restriction for both the unitary
and nonunitary parts. Its nonunitary argument uses strict positivity after
restriction of the relevant root cone. Consequently this reduction does not
take VII.2.2 or VII.2.3 temperedness statements as inputs. This differs from
Renard's route, which proves the unitary induced piece tempered using those
results; the separate piece module documents the implemented route.

All five hypotheses above are explicit premises of this supporting
implication. They have not been discharged here, and the conclusion is not
an unconditional theorem of `TemperedGeometricLemmaStatement`. Neither the
published target nor any of its imported files is changed. The independent
proof and publication obligations for the structural inputs and the exact
host proposition remain.
