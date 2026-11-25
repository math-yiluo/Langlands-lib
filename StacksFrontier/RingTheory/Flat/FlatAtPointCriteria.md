# Localization preserves flatness over the base

Module `StacksFrontier.RingTheory.Flat.FlatAtPointCriteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative algebra R → A, this file shows that localizing an A-module preserves flatness over R.

`Module.Flat.of_isLocalizedModule_of_tower` takes an A-linear map g : M → M′ exhibiting M′ as the localization of M at a submonoid of A, with compatible R-actions. If M is R-flat, then M′ is R-flat. The instances `Module.Flat.localizedModule_of_tower` and `Module.Flat.localizedModule_atPrime_of_tower` give this for the standard localized module and for localization at a prime of A.

The proof localizes the injective map obtained by tensoring an inclusion of R-modules with M, then uses tensor injectivity to conclude flatness. Denominators belong to A, and flatness is measured over the original ring R.

The reference is Tag 05UA.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/FlatAtPointCriteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
