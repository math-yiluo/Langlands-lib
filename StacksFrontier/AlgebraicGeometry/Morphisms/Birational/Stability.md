# Restriction of birational morphisms over an open of the target

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`IsBirational.morphismRestrict` says that a birational f : X ⟶ Y restricts to a birational morphism f⁻¹U ⟶ U (`f ∣_ U`) for any open U of Y.

The argument identifies the generic points of an open subscheme with the ambient generic points lying in it, and uses the canonical identification of the stalks of `f ∣_ U` with those of f; both steps are private lemmas of the file.

The module docstring announces stability under composition and coproducts, a converse criterion through an isomorphism over an open, and a lemma on the generic points of a coproduct; the file contains none of them. See also Tag 01RO.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Birational/Stability.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 3 are kept. The 4 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.IsBirational.comp`, `AlgebraicGeometry.isBirational_of_isIso_morphismRestrict`, `AlgebraicGeometry.isBirational_sigmaMap`, `AlgebraicGeometry.mem_genericPoints_sigmaι_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The one reference to EGA or SGA that the source writes as an attribute of that library belongs to a declaration left out; none remains.
