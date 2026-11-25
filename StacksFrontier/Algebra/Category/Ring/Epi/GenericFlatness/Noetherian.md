# Extensions of free modules and flat base change

Module `StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Noetherian`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file holds three private lemmas on free modules and flat base change. `StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Locus` imports it with `import all` and uses them.

- `free_of_shortExact`: let `A` be a ring and `0 → N₁ → N₂ → N₃ → 0` a short exact sequence of `A`-modules, given as maps `i`, `q` with `i` injective, `q` surjective and `Function.Exact i q`. If `N₁` and `N₃` are free, so is `N₂`: since `N₃` is free the sequence splits and `N₂ ≃ N₁ × N₃`. Unlike Mathlib's `ModuleCat.free_shortExact`, the three modules may lie in different universes.
- `baseChange_injective`, `baseChange_exact`: for a flat algebra `T` over `S`, base change `f ↦ f.baseChange T` preserves injectivity of a linear map and exactness of a pair of linear maps. They are Mathlib's `Module.Flat.lTensor_preserves_injective_linearMap` and `Module.Flat.lTensor_exact` restated for `LinearMap.baseChange`.

## Watch for

- The three lemmas are private, so a plain `import` of the module does not make them available.
- The module docstring is an overview of generic flatness (Stacks section 051Q): generic freeness over a Noetherian domain (Tag 051R), Tags 051S and 051T, the generic freeness locus of Equations 051U and 051V with Tags 051W, 051X and 051Y, and the route of the proofs. A second docstring says that the file proves Tag 051R. None of these results is declared in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Category/Ring/Epi/GenericFlatness/Noetherian.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 16 declarations of the source file 3 are kept. The 13 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 5 references to EGA and SGA that the source writes as attributes of that library were on declarations left out; none is listed above.
