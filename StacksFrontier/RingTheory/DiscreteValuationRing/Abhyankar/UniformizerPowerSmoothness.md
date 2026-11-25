# Formal smoothness from a uniformizer power equation

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.UniformizerPowerSmoothness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Consider an extension A → B of discrete valuation rings with fraction fields K → L, a finite extension K₁/K, and a field quotient E of L ⊗ₖ K₁. The file gives a sufficient condition for adic formal smoothness of a compatible extension S → T of DVRs with fraction fields K₁ and E. The square has local injective maps A → S and B → T.

`IsDiscreteValuationRing.formallySmoothNAdic_of_uniformizer_pow_eq` takes e = e(B/A) ≥ 2 and a uniformizer π of A. It assumes an element θ of K₁ with θᵉ equal to the image of π, and a surjective L-algebra map to E agreeing with the given map from K₁. If the residue characteristic of A is zero, or is coprime to e and κ(B)/κ(A) is separable, the map S → T is formally smooth for the maximal-ideal-adic topology on T, in any test-ring universe.

`surjective_of_isLocalHom_of_isFractionRing` shows that a local map R → S from a valuation ring R is surjective if S embeds over R into the fraction field of R. This is used to identify the DVRs with localizations of their respective integral closures. Other lemmas handle maximal-ideal contraction in integral squares and generation by the images of tensor factors.

The proof maps the canonical field obtained by adjoining an e-th root of π into K₁ and uses the image of θ to select a field quotient over L. It applies formal smoothness for the root extension to the intermediate DVRs and transfers it to S → T by finite base change.

The power hypothesis `hθ` is an exact equality in K₁ for the chosen π. The theorem takes the DVRs S and T and their compatible maps as inputs, and covers the root case with index at least two.

See Tag 0BRM. The helper `exists_integralClosure_hom_to_fractionRing` is a partial instance of EGA II 7.1.3, giving a map from an integral closure into an integrally closed model of the target field.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 7.1.3 | `exists_integralClosure_hom_to_fractionRing` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/UniformizerPowerSmoothness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 13 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_integralClosure_ringEquiv_of_isIntegral`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
