# The generic fibre of a normalized base change

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizedGenericFibre`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `f : X ⟶ Spec A`, `g : Spec B ⟶ Spec A` with `B` a domain with fraction field `L`, `W` the pullback of `f` along `g`, `W_L` its pullback to `Spec L`, and `r : Y ⟶ Spec B` the normalization of `W` followed by the projection. Both assume `hW`: quasi-compact opens of `W` have finitely many irreducible components.

- `isPullback_normalizationSchemeMap_normalization_comp_pullbackSnd`: the normalization of `W_L` is the base change of `r` to `Spec L`. No domain hypothesis on `B` is used here.
- `exists_dense_open_smooth_fiber_genericPoint_normalization_pullback`: assume `W ⟶ Spec B` locally of finite type. If a closed immersion `ρ` with nilradical kernel presents the reduction of `W_L` and carries a dense open smooth over `L`, then the fibre of `r` over the generic point of `Spec B` has a dense open smooth over the residue field there.

The proof pastes a cartesian normalization square along `Spec L ⟶ Spec B` with the pullback square.

The dense smooth open on the reduction is a hypothesis. References: Tags 09IL and 0307.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreNormalizedGenericFibre.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
