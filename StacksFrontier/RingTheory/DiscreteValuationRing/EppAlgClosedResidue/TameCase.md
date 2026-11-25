# Weak solutions in the tame case

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TameCase`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves elimination of ramification for complete discrete valuation rings in residue characteristic zero and in the tame case. It also relates the weak-solution condition to adic formal smoothness and to ramification indices on individual factors of the normalized base change.

## Results

- `exists_finite_extension_isWeakSolution_of_tame`, also named `exists_finite_extension_isWeakSolution_of_tame_or_charZero`, gives a finite separable extension of the base fraction field K that is a weak solution for A → B. Both DVRs must be maximal-ideal-adically complete. The hypothesis `htame` allows residue characteristic zero, or residue characteristic coprime to the ramification index e with separable residue extension.
- `isWeakSolution_of_tame_of_ramificationIndex_dvd` works with a prescribed finite K₁/K, which must lie in the same universe as K, under the same tame or characteristic-zero conditions. The hypothesis `hdvd` requires e to divide the local ramification index at each maximal ideal of the integral closure of A in K₁.
- `IntegralClosureBaseChange.isWeakSolution_of_formallySmoothNAdic` shows that if A → B is formally smooth for the maximal-ideal-adic topology, any package for a finite base extension is a weak solution. `isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField` applies this to weakly unramified DVR extensions with perfect base residue field.
- For a finite product presentation of the reduced tensor product compatible with the new base, `isWeakSolution_factor` extracts ramification index one at every maximal ideal of each factor’s normalization. `isWeakSolution_of_factors` proves the converse with the canonical maps from the new base normalization. Other lemmas transport index one along equivalences, and `exists_finite_extension_nonempty_algHom` embeds finitely many finite extensions of K into one finite extension in the universe of K.

The prescribed-extension proof uses Abhyankar’s lemma to obtain adic formal smoothness on each localized factor, then reads off index one. The existence proof takes K itself when e = 1 and otherwise adjoins an e-th root of a uniformizer. The factor comparison uses that projection to a component is flat and that integral closure commutes with finite products.

The elimination result is the complete tame and residue-characteristic-zero part of Tag 09F9. The formal-smoothness hypothesis `hformal` uses test rings in the maximum of the universes of A and B. The module docstring also announces algebraic closedness of the residue fields of finite extensions, which the file does not contain.

## References

Stacks Project Tag 09F9, Tag 09EQ for smoothness under base change, Tag 09E7 for the DVR smoothness criterion, and Tag 09EN(1) for weak solutions. The comments also refer to Tag 09ET, Tag 09F8 and Tag 09EJ. The product comparison is cited as a special case of EGA II 6.3.6.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.3.6 | `integralClosureBaseChangePiEquiv` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppAlgClosedResidue/TameCase.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 28 declarations of the source file 24 are kept. The 4 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.integralClosureTowerEquiv`, `IsDiscreteValuationRing.integralClosureTowerEquiv_apply`, `IsDiscreteValuationRing.isAlgClosed_of_ringEquiv`, `IsDiscreteValuationRing.isAlgClosed_residueField_of_finite`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
