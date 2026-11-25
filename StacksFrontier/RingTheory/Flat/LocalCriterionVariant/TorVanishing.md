# Tor vanishing for modules killed by an ideal power

Module `StacksFrontier.RingTheory.Flat.LocalCriterionVariant.TorVanishing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file develops the tensor-injectivity lemmas used in the ideal-adic local criterion for flatness.

Let I be an ideal of a commutative ring R. For an R-module M, assume M/IM is flat over R/I and multiplication I ⊗ᵣ M → M is injective. The private `Stacks.Flatness.LocalCriterionVariant.tor2_of_annihilated` gives Tor₁(M, Q) = 0 over R for each Q killed by a power of I. The private `Stacks.Flatness.LocalCriterionVariant.lTensor_subtype_injective_of_quotient_annihilated` deduces that M ⊗ᵣ P → M ⊗ᵣ F is injective whenever P is a submodule of F and F/P is killed by a power of I. Auxiliary lemmas track annihilation in quotients and the images of tensor maps into ideal multiples.

For Q killed by I, the Tor proof uses the first-variable vanishing lemma and a snake-lemma argument. It then inducts on the power of I using the submodule IQ and the quotient Q/IQ. The Tor conclusion is expressed as injectivity after tensoring the kernel inclusion of the canonical free presentation of M.

All declarations of the file are private; `StacksFrontier.RingTheory.Flat.LocalCriterionVariant.Criterion` uses them through `import all`. The module docstring presents the file as proving Tag 00ML and lists `Module.Flat.of_rTensor_subtype_injective_of_flat_quotient` as its main result, but that theorem is stated in `Criterion`.

The vanishing argument proves the part cited as Tag 051C (2). Tag 00M6 describes the tensor condition, and Tag 00ML is the local criterion these lemmas support.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/LocalCriterionVariant/TorVanishing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `Ideal.rTensor_subtype_map_injective`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
