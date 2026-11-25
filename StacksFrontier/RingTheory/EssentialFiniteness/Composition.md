# Ring maps essentially of finite presentation

Module `StacksFrontier.RingTheory.EssentialFiniteness.Composition`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines essential finite presentation for commutative ring maps and moves its witnesses between universes.

- `RingHom.EssentiallyOfFinitePresentation` means that the target of a ring map is the localization of a finitely presented algebra over its source. The map factors through that algebra by a compatible scalar tower, and the localization can invert any submonoid.
- `essFP_reuniverse` replaces a finitely presented localization witness by one in the maximum of the source and target universes. The proof writes the witness as a polynomial quotient, lifts that quotient to the required universe and transports the algebra and localization structures along the resulting isomorphism.

The finite-presentation definition fixes the intermediate algebra in `Type (max u v)` for a source in `Type u` and target in `Type v`, while allowing the two rings to lie in different universes. The module docstring still announces stability of both essential finiteness conditions under composition (Tag 07DS), and a section heading announces transport along universe lifts; neither is in the file.

## References

Tag 00QM for the definition.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/EssentialFiniteness/Composition.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 3 are kept. The 4 left out are not needed by the results for which the extract is made: `RingHom.EssentiallyOfFinitePresentation.ulift`, `essFP_descent`, `essFinitePresentation_comp`, `essFiniteType_comp`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
