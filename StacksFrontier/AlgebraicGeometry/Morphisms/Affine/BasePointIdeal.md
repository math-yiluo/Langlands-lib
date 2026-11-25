# The base prime from a stalk map

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Affine.BasePointIdeal`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For g : Y ⟶ Spec R, the prime of R under a point y of Y can be read from the germ of the structure map R → 𝒪(Y, y).

`germ_structureMap_eq` factors this germ through the localization at the prime of g(y), the base stalk isomorphism and the stalk map of g. Since the stalk map is local, `asIdeal_base_eq_comap_maximalIdeal` identifies the prime of g(y) with the contraction of the maximal ideal of 𝒪(Y, y).

`asIdeal_base_eq_comap_of_ringEquiv_localizationAtPrime` handles a model 𝒪(Y, y) ≃ T_q for a prime q of T. If the isomorphism carries the germ of each r ∈ R to the image in T_q of ι(r) for a ring map ι : R → T, the base prime is ι⁻¹(q). The compatibility with germs is the explicit hypothesis `hφ`.

References include Tag 01I1 and Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Affine/BasePointIdeal.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
