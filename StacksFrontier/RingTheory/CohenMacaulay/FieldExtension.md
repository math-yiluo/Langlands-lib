# Cohen–Macaulayness of isomorphic local rings

Module `StacksFrontier.RingTheory.CohenMacaulay.FieldExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`Stacks.CohenMacaulay.BaseFieldExtension.isMaximalCohenMacaulay_self_congr` says that Cohen–Macaulayness of a local ring depends only on its isomorphism class: for a ring isomorphism e : A ≃+* B of commutative local rings, `Module.IsMaximalCohenMacaulay A A` holds if and only if `Module.IsMaximalCohenMacaulay B B` does. The proof rewrites both sides with the invariance under e of the depth of a ring over itself along its maximal ideal and of the Krull dimension. No Noetherian hypothesis is needed.

The module docstrings present Tag 045M, that K ⊗ₖ L is Noetherian and Cohen–Macaulay for field extensions K/k and L/k one of which is finitely generated, and Tag 045N, invariance of Cohen–Macaulayness under a finitely generated extension of the base field, and announce results for them; none of these is in the file, whose only declaration is the lemma above.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/FieldExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 1 are kept. The 23 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- No reference to EGA or SGA remains: the 8 that the source writes as attributes of that library belong to declarations left out.
