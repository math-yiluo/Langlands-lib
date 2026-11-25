# Dimension of an injective integral extension

Module `StacksFrontier.RingTheory.KrullDimension.IntegralExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An injective integral extension of commutative rings preserves Krull dimension. The proof compares chains of prime ideals under contraction.

`Algebra.IsIntegral.ringKrullDim_eq` gives dim R = dim S for a commutative R-algebra S with `Algebra.IsIntegral R S` and `FaithfulSMul R S`. The latter class expresses injectivity of the structure map. The dimensions are in `WithBot ℕ∞`, including the bottom and infinite values.

The integrality inequality dim S ≤ dim R uses that contraction preserves strict inclusions of comparable primes. For dim R ≤ dim S, integrality and injectivity give surjectivity on spectra, and going-up lifts a prime chain one step at a time. The chain-lifting lemma produces a chain of the same length whose last prime contracts to the original last prime. Comparing the suprema of lengths gives the inequality.

The equality is Tag 00OK. Its proof uses Tag 00OJ for contraction, Tag 00GQ for surjectivity on spectra, Tag 00GU for going-up and the going-up case of Tag 00OH for the reverse inequality. The result is the injective case of EGA 0 16.1.5 and is also covered by EGA IV 5.4.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00OK](https://stacks.math.columbia.edu/tag/00OK) | `Algebra.IsIntegral.ringKrullDim_eq` | The source's ring inclusion `R ⊆ S` is stated as an `R`-algebra `S` with `algebraMap R S` injective, spelled `FaithfulSMul R S`; see the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.4.3 | `ringKrullDim_le_of_comap_surjective` | dim(A) ≤ dim(B) |
| EGA | 0 16.1.5 | `ringKrullDim_le_of_isIntegral` |  |
| EGA | IV 5.4.3 | `ringKrullDim_le_of_isIntegral` | dim(B) ≤ dim(A) |
| EGA | 0 16.1.5 | `Algebra.IsIntegral.ringKrullDim_eq` | ρ injective case |
| EGA | IV 5.4.3 | `Algebra.IsIntegral.ringKrullDim_eq` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/KrullDimension/IntegralExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
