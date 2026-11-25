# Ramification of cyclotomic quotient extensions

Module `StacksFrontier.NumberTheory.Cyclotomic.OneAddPow.RamificationCases`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a discrete valuation ring with characteristic-zero fraction field K and residue characteristic p. A map f from the integral pth cyclotomic ring to A supplies the root of unity. The file studies an extension L generated over K by z with P(z) = ξ for ξ in K and P a cyclotomic quotient polynomial.

`isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient` takes that equation, the generation hypothesis, a uniformizer π given as an irreducible element, and `hP`, which asserts `intProp`, `quotChar`, `shapeProp` and `funcEq` for P. It proves finiteness and Galoisness and gives four alternatives for L over K.

- Triviality is surjectivity of the structure map from K to L.
- The unramified case has degree p. Every maximal ideal of the integral closure lies over the maximal ideal of A, with ramification index one and separable residue extension.
- The totally ramified case uses `Stacks.KummerExtension.IsTotallyRamified` and gives index p at maximal ideals over the maximal ideal of A.
- In the residually inseparable case the integral closure is a DVR, with ramification index one and purely inseparable residue extension of degree p.

The theorem also gives sufficient conditions on ξ. An element of A gives the trivial or unramified case. A pole π to the power −n times a unit a gives total ramification when n is positive and p does not divide n. When n is positive and divisible by p, a numerator a whose residue is outside the pth powers gives the residually inseparable case.

The proof uses the Kummer degree bound and the ramification classification for Galois extensions of degree dividing p. Integral ξ gives an Artin–Schreier reduction, and the pole of order prime to p uses the earlier total-ramification result. For n = kp, the proof rescales z by πᵏ and uses an irreducible reduction of the form Xᵖ minus the residue of a to identify the integral closure and its residue field.

The hypothesis `hP` supplies the properties proved for a polynomial in Tag 09F2. The proof uses its `intProp` and `shapeProp` clauses. The valuation tests are implications, with the general disjunction also applying when a pole of order divisible by p has pth-power leading residue.

The ramification theorem is Tag 09F3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09F3](https://stacks.math.columbia.edu/tag/09F3) | `isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/NumberTheory/Cyclotomic/OneAddPow/RamificationCases.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
