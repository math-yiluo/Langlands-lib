# Finiteness of the extension of fraction fields

Module `StacksFrontier.RingTheory.OrderOfVanishing.Norm`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file holds one lemma, `finiteDimensional_fractionRing_of_finite`. Let A be a local domain with `Ring.KrullDimLE 1 A` and B a domain that is a finite A-module, with `hAB` asserting that A → B is injective. Let K and L be fraction fields of A and B, with L a K-algebra such that A → K → L and A → B → L are scalar towers. Then `Module.Finite K L`: L is a finite extension of K.

B is integral, hence algebraic, over A, so every nonzero element of B divides the image of a nonzero element of A. Hence L is already the localization of B at the image of the nonzero elements of A, and finiteness of B over A passes to the localizations. The proof does not use that A is local or of dimension at most one.

The module docstrings set out the order of vanishing of a norm and the determinant and length results behind it (Tags 02MD, 02MI, 02QH, 02M0); none of those results is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/OrderOfVanishing/Norm.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 46 declarations of the source file 1 are kept. The 45 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 12 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 15 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text. All 15 are on declarations left out; none is in the file.
