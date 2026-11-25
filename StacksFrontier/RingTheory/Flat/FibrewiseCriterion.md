# Flat permanence, extended ideals and faithful flatness over local maps

Module `StacksFrontier.RingTheory.Flat.FibrewiseCriterion`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves three lemmas about flatness along a ring map R → S, for an S-module M regarded as an R-module with `IsScalarTower R S M`.

- `Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat` is flat permanence: if M is flat over R and faithfully flat over S, then S is flat over R. The proof applies `Module.Flat.of_tensorProduct_of_faithfullyFlat` to M ⊗ₛ S ≅ M.
- `Stacks.Flatness.NoetherianFibreCriterion.injective_rTensor_subtype_map`: if M is flat over R and J is an ideal of R, then JS ⊗ₛ M → S ⊗ₛ M is injective, that is Tor₁^S(S/JS, M) = 0.
- `Stacks.Flatness.NoetherianFibreCriterion.faithfullyFlat_of_flat`: for a local homomorphism S → S′ of local rings, a finite nonzero S′-module that is flat over S is faithfully flat over S. Nakayama's lemma over S′ gives 𝔪_{S′}M ≠ M, and 𝔪_S M lies in 𝔪_{S′}M.

The second lemma is built from two maps of the same namespace: `smulMap`, the contraction N ⊗ᵣ P → N, n ⊗ p ↦ f(p)·n, along a linear form f : P → R, and `mulMap`, the S-linear multiplication S ⊗ᵣ J → S, whose range is JS (`range_mulMap`) and whose corestriction `mulMap'` is onto JS (`surjective_mulMap'`). By `smulMap_mulMap_apply`, contracting M ⊗ₛ (S ⊗ᵣ J) along `mulMap` is M ⊗ᵣ J → M across `TensorProduct.AlgebraTensorModule.cancelBaseChange`, which is injective because M is flat over R (`injective_smulMap_mulMap`); surjectivity of `mulMap'` carries this to JS ⊗ₛ M.

To watch for: the module docstring describes two fibrewise criteria of flatness, the nilpotent case (Tag 06A5) and the Noetherian local case (Tag 00MP), and lists both as main results; neither theorem is in the file. Despite its name, the namespace `Stacks.Flatness.NoetherianFibreCriterion` has no Noetherian hypothesis.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [039V](https://stacks.math.columbia.edu/tag/039V) | `flat_of_flat_of_faithfullyFlat` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 6.6.4 | `flat_of_flat_of_faithfullyFlat` | sufficiency, flat case |
| EGA | IV 2.5.5.4 | `faithfullyFlat_of_flat` | sufficiency |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/FibrewiseCriterion.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 42 declarations of the source file 17 are kept. The 25 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
