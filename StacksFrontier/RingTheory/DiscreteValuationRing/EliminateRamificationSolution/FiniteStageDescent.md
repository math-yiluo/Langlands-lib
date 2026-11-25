# Finite-stage descent for eliminating ramification

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.FiniteStageDescent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file supplies the descent arguments for the wild case. It passes from an algebraic extension of the base fraction field to finite intermediate fields and descends adic formal smoothness to their normalized local models.

## Results

- `exists_adjoin_range_eq_top_integralClosure_reducedTensor_finite_stage` assumes E/K is algebraic and the integral closure of B in the reduced tensor product L ⊗[K] E is of finite type over R. From some finite intermediate field onward, the image of each finite-stage integral closure generates the limit closure over R.
- `exists_reducedTensorProductScalarExtensionEquiv` identifies the scalar extension to E of the reduction of L ⊗[K] F with the reduction of L ⊗[K] E when the nilradical at F generates the nilradical at E (`hn`). The comparison agrees with the natural map on elements from the F-stage. `nilradical_map_eq_of_le_intermediateField` preserves this hypothesis upon enlarging F.
- `finite_integralClosure_tensorProduct_of_isGeometricallyReduced` makes the integral closure C of B in T finite over R ⊗[A] B. Here A → B is a local, essentially finite type map of DVRs, R is a Dedekind domain integral over and containing A, and T is essentially of finite type over R and geometrically reduced over its fraction field.
- `integralClosure_localRingHom_isDiscreteValuationRing_and_injective` shows that maximal ideals of the Noetherian integral closure of B in a reduced Artinian algebra over a field containing B contract to maximal ideals of R. Under the compatible DVR and integral Dedekind tower hypotheses, both localizations are DVRs and the local map is injective.
- `formallySmoothNAdic_localRingHom_of_bijective_tensorProduct` descends maximal-ideal-adic formal smoothness in a base-change square with four DVR localizations. It assumes a bijective tensor comparison (`hb`), compatible extension and contraction of the chosen maximal ideals, and injectivity of both local maps and the change of target.

Finite generation selects one stage in the directed cover. Tensoring a quotient identifies the relevant kernel, and finiteness of the normalization is checked at finitely many maximal ideals with nonzero contraction to R. Smoothness descends by faithful flatness for the maximal ideal equality and by the residue-field tensor comparison for separability.

The smoothness descent initially uses the maximum of the source and target universes for its test rings. `formallySmoothNAdic_of_formallySmoothNAdic_sameUniverse` gives arbitrary test universes for an injective local DVR map.

## References

Stacks Project Tag 09II and Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EliminateRamificationSolution/FiniteStageDescent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 26 declarations of the source file 24 are kept. The 2 left out are not needed by the results for which the extract is made: `Stacks.EliminateRamification.surjective_liftEquiv_of_adjoin_range_eq_top`, `Stacks.EliminateRamification.tensorProductEquivOfSurjectiveScalars_tmul`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
