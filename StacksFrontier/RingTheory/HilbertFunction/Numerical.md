# Numerical polynomials for local Hilbert functions

Module `StacksFrontier.RingTheory.HilbertFunction.Numerical`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite module M over a Noetherian local ring R and an ideal I whose radical is the maximal ideal 𝔪, the lengths of the successive I-adic quotients and the cumulative quotients are eventually given by binomial sums with integer coefficients.

## Results

`Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul`, also stated as `Stacks.HilbertFunction.NumericalPoly.solution`, gives eventual formulas for the R-lengths of IⁿM / Iⁿ⁺¹M and M / Iⁿ⁺¹M. Each formula is a linear combination of n choose i. The theorem supplies a common upper index by padding the two coefficient families with zeros. Under the same hypotheses, the proof establishes finiteness in every degree.

`binomPoly` represents n choose i by a rational polynomial of degree i. `binomSum` forms the rational polynomial of a finite integer combination and has degree equal to its top index when the corresponding coefficient is nonzero. The file also proves uniqueness of rational polynomials agreeing at all large natural numbers and additivity of extended length along nested submodules.

Finiteness follows from annihilation by powers of I and Artinianness of the corresponding ring quotients. The proof of polynomiality refines M ⊇ 𝔪ᵗM into cyclic steps killed by 𝔪, so each contribution is computed by the Hilbert function of a homogeneous polynomial-ring quotient over R / 𝔪. Length additivity gives the forward difference of the cumulative function, and Pascal’s identity gives its antidifference.

The private predicate `IsNumericalPoly` specializes the Stacks notion to functions ℕ → ℤ. The public theorem expresses finiteness explicitly by equating extended lengths to natural numbers before comparing their values in ℤ.

## References

Stacks Project, Tag 00K8, with Tag 00JX for the definition, Tag 00K3 for the cyclic calculation, and Tag 00JZ for antidifferences. EGA 0 16.2.1 covers the local case, and SGA 6 V 2.5 is cited for the binomial polynomials.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00K8](https://stacks.math.columbia.edu/tag/00K8) | `Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 6 V 2.5 | `binomPoly` |  |
| EGA | 0 16.2.1 | `Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul` | local case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertFunction/Numerical.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
