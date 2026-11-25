# Reducedness of localizations and of their field base changes

Module `StacksFrontier.RingTheory.GeometricallyReduced.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Three lemmas on reduced commutative rings.

- `isReduced_of_ringEquiv`: a ring isomorphic to a reduced ring is reduced.
- `isReduced_localization`: a localization B of a reduced ring A at a submonoid M is reduced. For a nilpotent b = a/s, some u ∈ M has u·aⁿ = 0, so (ua)ⁿ = 0, ua = 0 and b = 0.
- `isReduced_tensor_localization`: for a field k, a k-algebra R, a localization A of R at a submonoid M carrying a compatible k-algebra structure, and a field extension K/k, the ring K ⊗ₖ A is reduced whenever K ⊗ₖ R is. The proof sees (K ⊗ₖ R) ⊗_R A as a localization of K ⊗ₖ R and cancels the base change to identify it with K ⊗ₖ A. Here R and A share a universe.

The module docstring defines geometric reducedness over a field and announces that it passes to localizations and to polynomial rings in one variable; that predicate and those results are not in this file.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 1.2.8 | `isReduced_localization` |  |
| EGA | IV 10.10.4 | `isReduced_localization` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/GeometricallyReduced/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 3 are kept. The 6 left out are not needed by the results for which the extract is made: `GeometricallyReduced`, `geometricallyReduced_localization`, `geometricallyReduced_polynomial`, `isReduced_polynomial`, `isReduced_tensor_polynomial`, `tensorPolyRingEquiv`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above; the source's 7 others belong to declarations left out.
