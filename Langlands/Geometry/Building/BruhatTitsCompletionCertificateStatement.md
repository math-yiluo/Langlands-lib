# Completion certificate of KP Theorem 9.2.7

`BruhatTitsCompletionCertificateStatement` asserts that there is one
`KPBuildingAssignment` over all nonarchimedean local fields in universe `u`,
in either characteristic, that is valid and satisfies unramified descent.
The same assignment is used in both clauses.

- `KPBuildingAssignment.IsValid` is availability in the sense of corrected
  Definition 4.1.26. It includes Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8,
  4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22. The comparisons of 4.1.1 and
  4.1.17 concern the data assigned to the other groups and fields.
- `KPBuildingDatum.SatisfiesUnramifiedDescent` applies to the assigned datum
  for each connected reductive group. It identifies that datum's reduced
  building and the apartments of its maximal split tori with the fixed loci
  of the coefficient action upstairs. The action comes from a Galois-stable
  root-valuation apartment through `UnramifiedBuildingDescent.semilinearData`.
  The predicate identifies the lower affine roots with the set of nonconstant
  restrictions of upper affine roots and compares both families of integral
  models. The descent predicate explains the set-equality formulation of UR 3
  and the counterexample to the printed quantifier over each upper derivative.
  [Unramified descent of KP building data](FullValidity/UnramifiedDescent.md)

Theorem 9.2.7 certifies the descended building and models constructed
in §§9.2.1–9.2.5. The Lean statement takes its conclusion in existence
form on the Library's assignment interface. The values of the assignment
are constrained by the fixed-locus and model identifications in Axiom
4.1.27. The availability clause uses the ten axioms in the corrected
definition. The choice of the field scope follows `KPBuildingAssignment`.

Sources are Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Definition 4.1.26 and Axiom 4.1.27 (pp. 165–166, PDF pp. 196–197),
Theorem 9.2.7 (p. 329, PDF p. 360), and its assembly in §9.5
(pp. 363–364, PDF pp. 394–395). The coefficient action in §9.2.1
(pp. 325–326, PDF pp. 356–357) uses Axiom 4.1.17 and Proposition 7.9.5
(pp. 162 and 276, PDF pp. 193 and 307). The authors' *Corrections and additions*
(1 November 2024), PDF p. 27, give the ten-axiom list. PDF p. 39 revises
the Galois fixed-point arguments in §9.2.1.
