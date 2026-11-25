# A finite weakly unramified extension with prescribed residue field

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppWildCaseReduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file shows that every finite separable extension of the residue field of a discrete valuation ring is the residue field of a finite weakly unramified extension.

`Stacks.EppTheorem.exists_isWeaklyUnramified_residueField_algEquiv`: let A be a discrete valuation ring and E a finite separable extension of κ_A. Then there is a discrete valuation ring A₁ in the universe of A, finite as an A-module, such that A → A₁ is an extension of discrete valuation rings of ramification index one and the residue field of A₁ is κ_A-isomorphic to E.

The proof takes a primitive element of E, lifts its minimal polynomial to a monic P over A by `exists_monic_lift_map_residue_eq` and takes A₁ = A[X] ⧸ (P). The residue field is identified through `AdjoinRoot.residueFieldAlgEquiv` and `AdjoinRoot.algEquivOfPrimitiveElement`.

No completeness or henselian hypothesis on A is used. The module docstring also describes the compositum of κ_A with the perfect core, its use under Epp’s condition, the embedding into a henselian or complete B and separability over the fraction field; none of these is in the file.

References are Epp's *Elimination of wild ramification*, Stacks Project Tag 09F9 and Tag 09EJ, and EGA II 7.1.2 (partial).

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 7.1.2 | `exists_isWeaklyUnramified_residueField_algEquiv` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppWildCaseReduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 17 declarations of the source file 1 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
