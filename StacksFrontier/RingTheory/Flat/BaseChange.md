# Flatness under localized base change

Module `StacksFrontier.RingTheory.Flat.BaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Flatness can ascend through a pushout followed by localization. Descent is available under locality and flatness hypotheses on the square.

`Module.Flat.baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization` takes commutative algebras S and R′ over R, a pushout T, and a localization S′ of T. For an S-module M whose base change to S′ is M′, flatness of M over R implies flatness of M′ over R′. Conversely, flatness of M′ over R′ and of R′ over R imply flatness of M over R if S and S′ are local and S → S′ is local.

Ascent combines the flat base change to R′ with flatness of localization, and descent uses transitivity to obtain R-flatness of M′ before reflecting it along the faithfully flat map S → S′.

The theorem states parts (1) and (2) of Tag 00MQ. Parts (3) and (4) follow by taking M = S and M′ = S′. `IsBaseChange` permits an abstract model of the tensor product. The module docstrings also describe the descent of flatness along an injective map out of an Artinian ring (Tags 051J and 051L), which is not in the file.

References include Tag 00HI, Tag 00HT and Tag 00HR for base change, localization and faithful flatness.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00MQ](https://stacks.math.columbia.edu/tag/00MQ) | `baseChange_and_of_flat_baseChange_of_isPushout_of_isLocalization` | Parts (1) and (2). Of the source's eight locality assumptions only `IsLocalRing S`, `IsLocalRing S'` and `IsLocalHom (algebraMap S S')` are used, by part (2) alone, and they are bound inside the second conjunct together with `Module.Flat R R'`, so that part (1) is stated for an arbitrary commutative square; the rest are dropped. \"`S'` is a localization of `S ⊗_R R'`\" is `IsLocalization W S'` over an abstract pushout `Algebra.IsPushout R S R' T`, as in the siblings 00P4 and 00RJ, and `M' = S' ⊗_S M` is `IsBaseChange S' f`, as in 00MO. Parts (3) and (4) are the instance `M := S`, `M' := S'` and are not separate declarations. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/BaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 2 are kept. The 5 left out are not needed by the results for which the extract is made: `Module.Flat.of_flat_baseChange_of_injective`, `Stacks.Flatness.ArtinianDescent.flat_of_flat_tensorProduct_of_injective_of_isSemiprimaryRing`, `Stacks.Flatness.ArtinianDescent.flat_of_isSemisimpleRing`, `Stacks.Flatness.ArtinianDescent.solution`, `Stacks.Flatness.PushoutBaseChange.solution`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
