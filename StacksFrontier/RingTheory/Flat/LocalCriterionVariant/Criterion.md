# Noetherian local flatness and a tensor kernel comparison

Module `StacksFrontier.RingTheory.Flat.LocalCriterionVariant.Criterion`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves the ideal-adic local criterion for flatness and computes the tensor kernel that occurs when comparing the criterion across a change of rings.

Let R → S be a local homomorphism of Noetherian local rings. For a proper ideal I of R and a finite S-module M, `Module.Flat.of_rTensor_subtype_injective_of_flat_quotient` proves that M is R-flat if M/IM is flat over R/I and I ⊗ᵣ M → R ⊗ᵣ M is injective.

For an R-algebra R′ and an ideal J of R′ containing IR′, the private `Stacks.Flat.LocalCriterion.key` assumes M/IM is flat over R/I. An R′-linear map out of J ⊗ᵣ M that kills the image of the kernel of I ⊗ᵣ M → R ⊗ᵣ M also kills the kernel of J ⊗ᵣ M → R′ ⊗ᵣ M. Equivalently, that image generates the latter kernel over R′. The supporting tensor lemmas compare the kernel map with its form after base change.

The local criterion tests tensor injectivity on an arbitrary ideal inclusion. The nilpotent-quotient injectivity lemmas and Artin–Rees force every kernel element into every power of the extended ideal times the tensor module. Krull intersection over S then gives zero. For the kernel comparison, the proof lifts through a free presentation of M. After reduction modulo J, flatness over R/I lets it lift the relevant relation from the preimage of IF in the presentation, where F is the free module. Right exactness accounts for the remaining term.

In the local criterion, `hTor` is the tensor-injectivity form of first Tor vanishing, which allows R, S and M to lie in independent universes. The kernel comparison is stated in its annihilation form, with `hψ` expressing which image the test map kills.

## References

Tag 00ML gives the local criterion and Tag 00M6 its tensor formulation. The kernel comparison is the argument of Tag 00MM used toward Tag 00MO. The criterion cites EGA IV 11.3.12 (partial) and SGA 1 IV 5.6 ((ii) ⇒ (i), special case).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00ML](https://stacks.math.columbia.edu/tag/00ML) | `of_rTensor_subtype_injective_of_flat_quotient` | The hypothesis `Tor_1^R(M, R/I) = 0` is stated in the form Remark 00M6 identifies it with, the injectivity of `I ⊗_R M → R ⊗_R M`; this is the form the source's own second proof of the lemma assumes, and unlike `Tor_1` it puts `R` and `M` in no common universe. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 11.3.12 | `of_rTensor_subtype_injective_of_flat_quotient` | partial |
| SGA | 1 IV 5.6 | `of_rTensor_subtype_injective_of_flat_quotient` | (ii)⇒(i), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/LocalCriterionVariant/Criterion.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
