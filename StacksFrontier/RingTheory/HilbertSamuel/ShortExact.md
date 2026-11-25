# Hilbert–Samuel degrees in short exact sequences

Module `StacksFrontier.RingTheory.HilbertSamuel.ShortExact`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an ideal of definition I in a commutative Noetherian local ring, this file compares the Hilbert–Samuel polynomials and degrees of three finite modules in a short exact sequence.

## Results

`Ideal.max_degree_eq_degree_of_exact`, proved by `Stacks.HilbertSamuel.ShortExactDegree.solution`, takes an exact pair of linear maps M′ → M → M″ with the first injective and the second surjective. For rational polynomials P′, P, P″ eventually computing the respective lengths of the quotients by Iⁿ⁺¹, it gives deg P = max(deg P′, deg P″). If M′ has infinite length, it also gives deg(P − P″ − P′) < deg P′.

The theorem gives the same maximum formula directly for `Ideal.hilbertSamuelDegree` of the three modules. Taking I to be the maximal ideal gives the formula for `Module.hilbertSamuelDegree`.

Artin–Rees and length additivity bound P eventually from above by P′ + P″ and from below by P″ and a backward shift of P′. Nonnegative leading coefficients prevent cancellation in the sum. For the error bound, the characteristic-function formula gives P = P″ + Q(X − c) + l, with Q the Hilbert–Samuel polynomial of a finite-colength submodule of M′. The shift changes only lower-degree terms, the finite-colength comparison bounds deg(Q − P′), and the constant l has smaller degree because P′ has positive degree.

The polynomial comparison quantifies over computing polynomials with explicit hypotheses, bundled in the proof as `Computes`. These assert that the extended lengths are finite and equal to the polynomial evaluations for all large natural n. For the invariant equality, existence comes from the binomial formula for the local Hilbert function and uniqueness from eventual agreement on natural numbers. Degrees live in `WithBot ℕ`, with −∞ for zero.

## References

Stacks Project, Tag 00KC, with Tag 00IN for Artin–Rees, Tag 00K6 for the characteristic-function formula, Tag 00K8 for existence, Tag 00KA for the degree, and Tag 00KB for finite colength. EGA 0 16.2.1 and EGA 0 16.2.2.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00KC](https://stacks.math.columbia.edu/tag/00KC) | `Ideal.max_degree_eq_degree_of_exact` | The first conjunct is parts (1) and (2) of the tag, for polynomials computing the three Hilbert–Samuel functions as in Tags 00K8 and 00K9, so `χ_{I,M} - χ_{I,M''} - χ_{I,M'}` is `P - P'' - P'`; that this is again a numerical polynomial is inherited from the hypotheses on the three polynomials, and the degree bound is the content. The second conjunct is part (2) for the invariant of Definition 00KA, and part (3) of the tag is its case `I = maximalIdeal R`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.2.1 | `Computes` |  |
| EGA | 0 16.2.1 | `exists_computes` | special case |
| EGA | 0 16.2.2.2 | `Ideal.max_degree_eq_degree_of_exact` | (1) deg bound, (2) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertSamuel/ShortExact.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
