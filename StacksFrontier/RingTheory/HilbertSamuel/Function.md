# Characteristic and Hilbert functions in exact sequences

Module `StacksFrontier.RingTheory.HilbertSamuel.Function`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file compares the cumulative and graded lengths of I-adic filtrations over a commutative Noetherian local ring R. The main results take I to be an ideal of definition, with radical equal to the maximal ideal.

## Definitions and results

`chi` and `charFn` assign to n the extended length of M / Iⁿ⁺¹M. The function `hilbertFn` assigns the extended length of IⁿM / Iⁿ⁺¹M. For finite M and an ideal of definition, `length_quot_pow_ne_top` and `charFn_ne_top` show that the lengths of the quotients M / IᵏM are finite.

- `additivity_of_characteristic_and_hilbert_functions` treats a short exact sequence 0 → M′ → M → M″ → 0 of finite modules. It finds N ⊆ M′ of finite colength l and a shift c, so for n ≥ c the characteristic function of M is χ(M″, n) + χ(N, n − c) + l. The Hilbert function of M is φ(M″, n) + φ(N, n − c).
- `HilbertSamuel.degree_sub_lt` shows that, for a finite module M of infinite length and a submodule M′ of finite colength, the difference of their Hilbert–Samuel polynomials has degree strictly below both degrees.

Finiteness comes from the Artinian quotients R / Iᵏ. Artin–Rees identifies the induced filtration for the exact sequence, and additivity of quotient lengths gives the characteristic formula. Consecutive values give the Hilbert formula. For the polynomial comparison, upper and shifted lower length bounds force equality of degrees and leading coefficients.

`HilbertSamuel.hilbertSamuelFunction` converts extended lengths to natural numbers using `ENat.toNat`. Its interpretation as length uses the finiteness hypotheses. The degree comparison takes `hχM` and `hχM'` as hypotheses that the supplied rational polynomials eventually compute this function, expressed by `HilbertSamuel.IsHilbertSamuelPoly`. The module docstring still lists, as a main result, a two-sided comparison of χ for a submodule of finite colength, which is not in the file.

## References

Stacks Project, Tag 00K6 and Tag 00KB. EGA 0 16.2.1, 0 16.2.2.2, III 4.3.13, IV 2.5.7, IV 6.1.3, IV 21.10.13 and IV 21.13.12.1. SGA 1 I 2.1, 3 VIIB 0.4.2, 3 X 3.8 and 6 X 1.1.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00K6](https://stacks.math.columbia.edu/tag/00K6) | `additivity_of_characteristic_and_hilbert_functions` |  |
| [00KB](https://stacks.math.columbia.edu/tag/00KB) | `degree_sub_lt` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.2.1 | `length_quot_pow_ne_top` | special case |
| SGA | 6 X 1.1.2 | `length_quot_pow_ne_top` | special case |
| EGA | 0 16.2.1 | `IsIdealOfDefinition` |  |
| EGA | III 4.3.13 | `IsIdealOfDefinition` |  |
| EGA | IV 21.13.12.1 | `IsIdealOfDefinition` |  |
| EGA | IV 6.1.3 | `IsIdealOfDefinition` |  |
| SGA | 1 I 2.1 | `IsIdealOfDefinition` |  |
| EGA | 0 16.2.1 | `IsHilbertSamuelPoly` |  |
| SGA | 3 VIIB 0.4.2 | `HasFiniteLength` |  |
| EGA | 0 16.2.1 | `length_quotient_lt_top` | finite length of M/q^nM |
| EGA | IV 21.10.13 | `length_quotient_lt_top` | (i) |
| EGA | IV 2.5.7 | `inj_of_surj_of_length_eq` | special case |
| SGA | 3 X 3.8 | `inj_of_surj_of_length_eq` | Finite abelian groups |
| EGA | 0 16.2.2.2 | `degree_sub_lt` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertSamuel/Function.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 43 declarations of the source file 40 are kept. The 3 left out are not needed by the results for which the extract is made: `c2_existence`, `chi_bounds_of_quotient_finiteLength`, `hilbertFn_ne_top`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 14 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
