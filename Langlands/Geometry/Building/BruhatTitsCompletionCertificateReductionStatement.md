# The completion certificate from availability and unramified descent

`BruhatTitsCompletionCertificateReductionStatement` says that the availability
statement and the existence of equivalent descended data in
`UnramifiedDescentOfGroupAxiomsStatement` together imply
`BruhatTitsCompletionCertificateStatement`. The scope of all three
propositions is connected reductive groups over nonarchimedean local fields
of either characteristic in universe `u`.

The implication is derived from the two conclusions of KP Theorem 9.2.7
with corrected Definition 4.1.26 and the set-equality form of UR 3.
The proof `bruhatTitsCompletionCertificateReduction` takes the assignment
and its validity from `BruhatTitsAvailabilityStatement`. For each group,
`KPBuildingAssignment.IsAvailableFor.groupAxioms` gives the one-group
premise on the assigned datum. The descent hypothesis supplies a
group-valid descended datum and a building equivalence over the identity
of the rational point group. The proof chooses these data as a dependent
family and assembles them into a new assignment with
`KPBuildingAssignment.ofData`. The theorem
`KPBuildingAssignment.ofData_isValid` transfers the comparisons of
Axioms 4.1.1 and 4.1.17 across the equivalences. The chosen data supply
the remaining group axioms and the descent clause for that assignment.

Sources are Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Axiom 4.1.27 (pp. 165–166, PDF pp. 196–197), Theorem 9.2.7 (p. 329,
PDF p. 360), Proposition 9.4.28 (pp. 359–360, PDF pp. 390–391) and §9.5
(pp. 363–364, PDF pp. 394–395). The authors' *Corrections and additions*
(1 November 2024), PDF p. 27, supply the corrected availability axioms
in Definition 4.1.26. PDF p. 39 revises the Galois fixed-point arguments
in §9.2.1.
