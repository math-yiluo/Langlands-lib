# Maximal-ideal completions as input to Epp descent

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionInput`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file supplies the properties of the actual maximal-ideal-adic completion Â of a discrete valuation ring A that are needed in Epp’s completion step. It also applies the finite separable extension descent to these completions and records that completing a noetherian local ring does not change its residue field.

- `exists_isDomain_isDiscreteValuationRing_adicCompletion` and `ringKrullDim_adicCompletion_eq_one` give the domain and DVR properties and dimension one for a DVR A. Instances make A → Â a DVR extension.
- `AdicCompletionFractionField` is the fraction field of Â. For any fraction field K of A, `algebraAdicCompletionFractionField` extends A → Frac(Â) to K. The associated tower lemma gives compatibility with the map from A.
- `isWeaklyUnramified_adicCompletion` gives ramification index one, and `formallySmoothNAdic_algebraMap_adicCompletion` gives adic formal smoothness of A → Â.
- `exists_finite_separable_extension_tensorProduct_equiv_of_isDVR` shows that a finite separable extension M of a fraction field K̂ of Â is K̂-isomorphic to K̂ ⊗[K] L for a finite separable intermediate field L of an algebraic closure of K.
- For a noetherian local ring B, `surjective_algebraMap_residueField_adicCompletion` shows that κ_B → κ_B̂ is surjective, after `algebraMap_residueField_adicCompletion_eq_map` identifies it with `ResidueField.map`; `expChar_residueField_adicCompletion` carries an exponential characteristic of κ_B over to κ_B̂.

A uniformizer remains a uniformizer under completion, and the map of residue fields induced by completing a noetherian local ring is an isomorphism. Together they give adic formal smoothness by Tag 09E7. The extension descent applies Krasner’s theorem using the domain and dimension results.

The DVR result uses the forward direction of Tag 0AP1. The Krasner application retains separability of M/K̂. The module docstring also announces henselianness of Â, a packaged form of the fraction-field tower and a later result consuming the residue-field statement; the file contains none of them.

References include Tag 09F9, Tag 09EJ and Tag 09EQ, and SGA 4 X 2.2.1 for the fraction field and EGA 0 19.3.6 a)⇒b) with B = A for formal smoothness.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 4 X 2.2.1 | `AdicCompletionFractionField` |  |
| EGA | 0 19.3.6 | `formallySmoothNAdic_algebraMap_adicCompletion` | a)⇒b) with B = A |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppCompletionInput.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 23 declarations of the source file 19 are kept. The 4 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_algebra_isScalarTower_adicCompletionFractionField`, `IsDiscreteValuationRing.exists_isExtension_adicCompletion`, `IsDiscreteValuationRing.henselianLocalRing_adicCompletion`, `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algHom_of_adicCompletion`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above; a third belonged to a declaration left out.
