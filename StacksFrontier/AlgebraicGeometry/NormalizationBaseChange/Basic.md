# Normalization along flat morphisms

Module `StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A flat morphism of schemes induces a morphism between the normalizations of its source and target.

In `AlgebraicGeometry`, `mem_genericPoints_of_generalizingMap` shows that a map lifting generalizations between quasi-sober T₀ spaces sends generic points of irreducible components to generic points, and `Scheme.Hom.mem_genericPoints_of_flat` applies this to a flat morphism of schemes. For a flat morphism `f`, `Scheme.Hom.genericPointResidueSpectrumMap` uses the corresponding residue-field maps to give a morphism between the coproducts of the generic-point residue spectra; `Scheme.Hom.ι_genericPointResidueSpectrumMap` describes it on each summand, and `Scheme.Hom.genericPointResidueSpectrumMap_fromGenericPointResidueFields` shows that it lies over `f`. The definition `normalizationSchemeMap` induces the map of normalizations `X.normalizationScheme hX ⟶ Y.normalizationScheme hY` when quasi-compact opens on each scheme have finitely many irreducible components. The theorem `normalizationSchemeMap_normalization` gives its commutation with the normalization morphisms `stacksNormalization`.

A flat morphism lifts generalizations, which gives the generic-point result. The map of normalizations comes from functoriality of relative normalization applied to the square over `f`.

The module docstring also announces the base change of the normalization to an extension field `K/k` and the comparison morphism of Tag 0C3N; they are not in this file.

EGA IV 2.3.4 and SGA 3 X 5.14.0 are attached to `Scheme.Hom.mem_genericPoints_of_flat`, the generic-point result for flat morphisms of schemes.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.3.4 | `Hom.mem_genericPoints_of_flat` | (iii), special case |
| SGA | 3 X 5.14.0 | `Hom.mem_genericPoints_of_flat` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 7 are kept. The 7 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.baseChangeNormalization`, `AlgebraicGeometry.flat_pullback_fst_specMap_algebraMap`, `AlgebraicGeometry.flat_specMap_algebraMap`, `AlgebraicGeometry.normalizationBaseChangeComparison`, `AlgebraicGeometry.normalizationBaseChangeComparison_comp_baseChangeNormalization`, `AlgebraicGeometry.normalizationBaseChangeComparison_comp_fst`, `AlgebraicGeometry.normalizationBaseChangeComparison_comp_snd`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
