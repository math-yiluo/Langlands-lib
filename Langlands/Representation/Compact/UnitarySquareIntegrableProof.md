# Renard IV.2.2 and IV.3.2–IV.3.3: the combined proof

Author: Worker 89.

The theorem `Langlands.Renard.CompactRepresentation.unitarySquareIntegrable`
proves the exact published proposition `UnitarySquareIntegrableStatements`,
with independent group and representation-carrier universes. It assembles the
five component proofs by conjunction introduction, in the order of the
published proposition.

| Component proposition | Imported proof |
| --- | --- |
| `UnitaryAdmissibleEndomorphismStatement` | `unitaryAdmissibleEndomorphism` |
| `EssentiallySquareIntegrableAdmissibleStatement` | `essentiallySquareIntegrableAdmissible` |
| `SquareIntegrableUnitarySemisimpleStatement` | `squareIntegrableUnitarySemisimple` |
| `SchurOrthogonalityStatement` | `schurOrthogonality` |
| `CoefficientLinearIndependenceStatement` | `coefficientLinearIndependence` |

Each imported theorem proves its component as stated. The conjunction therefore
retains every quantifier and hypothesis, including first countability in the
endomorphism criterion, the supplied Borel Haar and right-invariant measure
on the central quotient in the IV.3 statements, and the published smooth
representation, dual, twist and coefficient definitions. The Schur component
includes integrability in both relations and existence of a positive real
formal degree. No premise is added.

The individual implemented arguments are explained in
[UnitaryAdmissibleEndomorphismProof.md](UnitaryAdmissibleEndomorphismProof.md),
[EssentiallySquareIntegrableAdmissibleProof.md](EssentiallySquareIntegrableAdmissibleProof.md),
[SquareIntegrableUnitarySemisimpleProof.md](SquareIntegrableUnitarySemisimpleProof.md),
[SchurOrthogonalityProof.md](SchurOrthogonalityProof.md), and
[CoefficientLinearIndependenceProof.md](CoefficientLinearIndependenceProof.md).
This module supplies only their logical assembly.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.2.2 Corollary (i), printed p.98 /
PDF p.104, and IV.3.2–IV.3.3, printed pp.100–102 / PDF pp.106–108.
Registered source ID:
`renard-2026-representations-groupes-reductifs-padiques`;
SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
