# Flatness at a stage of a directed system

Module `StacksFrontier.RingTheory.SpreadingOut.Flat`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file descends flatness of a colimit module to stages of a directed system of local rings and finite modules with compatible base changes.

## Results

`Module.Flat.exists_ge_flat_of_isColimit` takes a system of local maps Aᵢ → Bᵢ of local rings with finite Bᵢ-modules Nᵢ, compatible colimits R → S and M, and M flat over R. Each Aᵢ is essentially of finite type over ℤ and Aᵢ → Bᵢ is essentially of finite type. For each transition i ≤ j, Bⱼ is a prime localization of the ring pushout and Nⱼ is the base change of Nᵢ. With local transitions on A, the theorem gives for every i some j ≥ i with Nⱼ flat over Aⱼ via the stage map.

`CommRingCat.exists_isLocalization_tensorProduct_of_pushout` transports the ring localization condition to the tensor product. Its hypothesis `hmap` identifies the algebra map from the tensor product with the product map. The conclusion gives a localization at a submonoid of the tensor product.

## Proof

Noetherianity gives finitely many generators for the maximal ideal of Aᵢ and for their module of relations on Nᵢ, and flatness of M makes those generating relations trivial at a common later stage. The local flatness criterion uses the resulting vanishing on the tensor kernel together with flatness of the quotient module over the residue field of Aᵢ.

## Scope

The theorem takes the colimit system as data, including `hBloc` for the localization and `hNbc` for module base change. `hAmaplocal` ensures the maximal ideal of Aᵢ extends to a proper ideal of Aⱼ. The index, rings and modules use a common universe.

## References

Tag 00R6 for flatness at a stage, Tag 00QX for the form of the system and Tag 00MO for the local criterion.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00R6](https://stacks.math.columbia.edu/tag/00R6) | `exists_ge_flat_of_isColimit` | The system \"as in Lemma 00QX\" is spelled out as the data and the six conditions concluded by `RingHom.EssentiallyOfFinitePresentation.exists_isColimit_\ essFiniteType_module`, together with locality of the transition maps `A i → A j`, which is the source's \"system of local homomorphisms of local rings\" read as a system in the category of local rings and is what 00MO needs to know `(𝔪 i) A j` is proper. The hypotheses of 00QX are not assumed, being either unused or consequences of the system. The conclusion is the cofinal form (`∀ i, ∃ j ≥ i`), which is what the source's proof produces and what the dependents use. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/SpreadingOut/Flat.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
