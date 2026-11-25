# Noetherianity of the associated graded module

Module `StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.GradedNoetherian`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves that the associated graded module of an ideal-power filtration is Noetherian over a polynomial ring. It also computes the degree components of polynomial actions on leading forms.

For a commutative ring S, choose a finite family aᵢ generating J and assume S/J is Noetherian. The lemma `grModule_noetherian` gives Noetherianity of `grModule S J` as a module over the polynomial ring over S/J on that family of variables, with the action `grModulePModule`. The degree-zero class of 1 generates the module because each Jⁿ is spanned by the degree-n monomials in the aᵢ. The Hilbert basis theorem makes the polynomial ring Noetherian.

With the same generating family, `monomial_smul_lof_grMk` says that a monomial of degree d acts on the class of w in degree m by multiplying by the corresponding product of the aᵢ, scaling by the monomial coefficient, and raising degree to m + d. For any polynomial, `component_smul_lof` expresses the degree-N component of its action on that class as the class of sw in Jᴺ/Jᴺ⁺¹ for some s in J to the power N − m. Only monomials of matching degree contribute, and their coefficients are lifted from S/J to S. Here subtraction is in the natural numbers. The component computation works for arbitrary S/J.

The helper `sub_sum_mem_of_grMk_eq_sum` turns a sum identity of degree-N classes back into a congruence modulo Jᴺ⁺¹. The Noetherianity result is a special case cited at SGA 5 V 5.1.6.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 5 V 5.1.6 | `grModule_noetherian` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/NoetherianRing/GradedNoetherian.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
