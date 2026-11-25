# Hilbert functions of homogeneous polynomial-ring quotients

Module `StacksFrontier.RingTheory.HilbertFunction.PolynomialQuotient`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a polynomial ring S = k[X₁, …, X_d] over a field k, with each variable in degree one, this file sets up the graded pieces of S and the Hilbert function of a quotient S/I.

## Results

- `instGradedAlgebra` registers Mathlib’s total-degree grading `MvPolynomial.gradedAlgebra` as an instance, so that `Ideal.IsHomogeneous` applies to ideals of `MvPolynomial (Fin d) k`.
- `gradedPieceS` is the space Sₙ of homogeneous polynomials of degree n. `gradedPieceI` is I ∩ Sₙ as a k-subspace, for any ideal I. `hilbertFunction` subtracts their dimensions in ℕ.
- `binomialPoly i` is the rational polynomial X(X − 1)⋯(X − i + 1)/i!, and `binomialPoly_eval` proves that its value at q ∈ ℚ is `Ring.choose q i`.

The docstring of `hilbertFunction` identifies it with the dimension of (S/I)ₙ; the file does not prove this. The module docstring states the degree bound of Tag 00K3 for a nonzero graded ideal, and a later comment outlines its proof; neither the bound nor its lemmas are in the file.

## References

EGA 0 15.1.1 is cited for the standard grading as a special case.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 15.1.1 | `instGradedAlgebra` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertFunction/PolynomialQuotient.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 6 are kept. The 9 left out are not needed by the results for which the extract is made: `Stacks.HilbertFunction.PolynomialQuotient.degree_le_of_eventually_le`, `Stacks.HilbertFunction.PolynomialQuotient.exists_finrank_gradedPieceI_ge`, `Stacks.HilbertFunction.PolynomialQuotient.exists_polynomial_choose_diff`, `Stacks.HilbertFunction.PolynomialQuotient.finrank_gradedPieceS`, `Stacks.HilbertFunction.PolynomialQuotient.hilbertFunction_eq_finrank_quotient`, `Stacks.HilbertFunction.PolynomialQuotient.hilbertFunction_le_choose_diff`, `Stacks.HilbertFunction.PolynomialQuotient.isNumericalPolynomial_degree_lt_of_le`, `Stacks.HilbertFunction.PolynomialQuotient.leadingCoeff_nonneg_of_eventually_nonneg`, `Stacks.HilbertFunction.PolynomialQuotient.leadingCoeff_nonpos_of_eventually_nonpos`.
- 4 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
