# Krull dimension under integral ring maps

Module `StacksFrontier.RingTheory.KrullDimension.GoingUpGoingDown`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an integral homomorphism of commutative rings, the file compares the Krull dimensions of source and target and shows that closed points contract to closed points.

`integral_dim_up` takes a ring map f : R → S with `f.IsIntegral` and proves `ringKrullDim S ≤ ringKrullDim R`, and that every closed point of Spec S is sent by `PrimeSpectrum.comap f` to a closed point of Spec R. Its two parts use incomparability of primes over the same prime, which makes contraction along f strictly monotone on Spec S (Mathlib's `Ideal.IsIntegral.under_lt_under`), and contraction of maximal ideals under integral maps (`Ideal.isMaximal_under_of_isIntegral_of_isMaximal`). No injectivity, surjectivity or finiteness of f is assumed.

The result is Tag 00OJ. References for the integral case are EGA 0 16.1.5 and EGA IV 4.1.2(ii), 5.4.2, 5.4.3, 5.5.1, 5.5.2 and 5.6.6. The module docstrings of the file also describe dimension inequalities under going up or going down and the maximality of contractions under going up (Tags 00OH and 00OI); none of these is in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00OJ](https://stacks.math.columbia.edu/tag/00OJ) | `integral_dim_up` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.1.5 | `integral_dim_up` | dim(B) ≤ dim(A) |
| EGA | IV 4.1.2 | `integral_dim_up` | (ii), special case |
| EGA | IV 5.4.2 | `integral_dim_up` | Affine case |
| EGA | IV 5.4.3 | `integral_dim_up` | dim(B) ≤ dim(A) |
| EGA | IV 5.5.1 | `integral_dim_up` | special case |
| EGA | IV 5.5.2 | `integral_dim_up` | special case |
| EGA | IV 5.6.6 | `integral_dim_up` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/KrullDimension/GoingUpGoingDown.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 1 are kept. The 7 left out are not needed by the results for which the extract is made: `chain_lift_goingDown`, `chain_lift_goingUp`, `comap_isMaximal_of_goingUp`, `krullDim_le_of_chain_lift`, `lt_of_le_of_comap_ne`, `ringKrullDim_le_of_goingDown`, `ringKrullDim_le_of_goingUp`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 7 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
