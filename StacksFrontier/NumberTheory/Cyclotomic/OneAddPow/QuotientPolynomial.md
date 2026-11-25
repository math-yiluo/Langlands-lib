# The cyclotomic quotient polynomial

Module `StacksFrontier.NumberTheory.Cyclotomic.OneAddPow.QuotientPolynomial`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let p be prime and let f map the integral cyclotomic ring ℤ[ζₚ] to a commutative ring A. The file constructs a polynomial over A representing the quotient of (1 + wX)ᵖ − 1 by wᵖ and proves its two-variable addition law.

`zetaA` is the image of the standard cyclotomic generator, and `wElt` is w = 1 − ζ for that image ζ. The polynomial `Pcand` is the product of X + uₖ for 0 ≤ k < p, where `uElt` defines uₖ as the sum of the first k powers of ζ starting at 1.

`main_statement` gives a single polynomial P with all four properties.

- `intProp` gives wᵖP = (1 + wX)ᵖ − 1 in A[X], degree at most p, constant coefficient zero, and the coefficient equations. For 0 < i ≤ p, the product of the ith coefficient and the (p − i)th power of w is the binomial coefficient p choose i.
- `quotChar` gives the quotient identity after inverting w.
- `shapeProp` writes P as Xᵖ − X plus terms in degrees 1 through p − 1 whose coefficients lie in (w).
- `funcEq` gives P(x + y + wxy) = P(x) + P(y) + wᵖP(x)P(y) in the polynomial ring in two variables.

The factorization of Xᵖ − 1 gives the identity for `Pcand`. The coefficient equations and addition law use cancellation over the universal cyclotomic domain and then map to A. For the shape, the proof reduces the factors modulo (w), where ζ becomes 1 and their product is Xᵖ − X.

The root in A is specified by the map f and can have order smaller than p. The linear coefficient is −1 modulo (w), and the coefficient equation for i = p makes the top coefficient 1. `quotChar` constrains P only after inverting w, which gives the zero ring when w is nilpotent; integrality over A is `intProp`. The docstrings of `quotChar`, `intProp` and `main_statement`, a comment and the heading of an empty section about an example over ℤ/4 refer to lemmas that are not in the file.

The existence theorem is Tag 09F2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09F2](https://stacks.math.columbia.edu/tag/09F2) | `main_statement` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/NumberTheory/Cyclotomic/OneAddPow/QuotientPolynomial.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 43 declarations of the source file 34 are kept. The 9 left out are not needed by the results for which the extract is made: `adjoin_sq_eq_one_eq_bot`, `coeff_eq_one_of_intProp`, `cyclotomicRingTwoEquivInt`, `natCast_eq_zero_of_intProp`, `not_intProp_toZMod4_zero`, `quotChar_of_isNilpotent`, `quotChar_toZMod4`, `toZMod4`, `wElt_eq_two`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
