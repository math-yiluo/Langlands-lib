# Proof of the Bruhat–Tits completion certificate

`Langlands.Geometry.Building.bruhatTitsCompletionCertificate` proves
`BruhatTitsCompletionCertificateStatement.{u}` for arbitrary `u`. One
assignment for connected reductive groups over nonarchimedean local fields
of either characteristic satisfies all ten axioms of corrected Definition
4.1.26. Its datum for each group also satisfies Axiom 4.1.27, with UR 3
expressing that the lower affine roots are exactly the nonconstant
restrictions of the upper affine roots.
[Statement](BruhatTitsCompletionCertificateStatement.md)

The Lean proof applies `bruhatTitsCompletionCertificateReduction` to
`bruhatTitsAvailability` and `unramifiedDescentOfGroupAxioms`. The first
theorem supplies a valid assignment. The second gives a group-valid
descended replacement for each datum satisfying the one-group axioms,
together with an equivariant equivalence of reduced buildings over the
identity on rational points.
[Availability](BruhatTitsAvailabilityProof.md)
[Descent](UnramifiedDescentOfGroupAxiomsProof.md)

The reduction assembles the replacements into one assignment.
`KPBuildingAssignment.ofData_isValid` transfers the comparisons of Axioms
4.1.1 and 4.1.17 along the building equivalences. The chosen replacements
supply the one-group axioms and the descent clauses for that same assignment.
[Reduction](BruhatTitsCompletionCertificateReductionStatement.md)

## Sources

- Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  See Definition 4.1.26 and Axiom 4.1.27 (pp. 165–166, PDF pp. 196–197),
  Theorem 9.2.7 (p. 329, PDF p. 360), the paragraph introducing
  Proposition 9.4.28 (p. 359, PDF p. 390), and §9.5 (pp. 363–364, PDF pp. 394–395).
- Kaletha and Prasad, *Corrections and additions* (1 November 2024),
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
  PDF p. 27 gives the corrected axiom list. PDF p. 39 revises the Galois
  fixed-point arguments of §9.2.1.
