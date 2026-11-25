# Galois degree of a cyclotomic quotient extension

Module `StacksFrontier.NumberTheory.Cyclotomic.OneAddPow.GaloisDegree`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A root of a cyclotomic quotient polynomial gives a Kummer generator after an affine change of variable. The file proves the resulting Galois and degree statement and develops a separable-reduction criterion for later ramification arguments.

`cyclotomic_galois_and_degree` takes a domain A with fraction field K of characteristic zero, a prime p, and a map from the integral pth cyclotomic ring to A. It assumes `hP : intProp f P` for the polynomial P and that L is generated over K by an element z satisfying P(z) = ξ for ξ in K. It supplies a finiteness witness for L over K, proves the extension Galois and shows that the degree divides p.

The proof checks that the cyclotomic generator stays primitive in K and that b = 1 + wz generates L, where w is one minus that root. The polynomial identity in `hP` gives bᵖ = 1 + wᵖξ in K, so the Kummer theorem applies.

The private `unramified_or_trivial_of_separable_reduction` assumes a DVR, a finite Galois extension of degree dividing p and a generating root of a monic polynomial with separable reduction. It gives triviality or degree p with ramification index one and separable residue extension at every maximal ideal of the integral closure. Other private lemmas show that any polynomial P satisfying `shapeProp f P` reduces to Xᵖ − X when A is local with residue characteristic p.

The public theorem gives the Galois and degree part of Tag 09F3 and requires only the domain and characteristic-zero fraction field hypotheses on the base for that part.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/NumberTheory/Cyclotomic/OneAddPow/GaloisDegree.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
