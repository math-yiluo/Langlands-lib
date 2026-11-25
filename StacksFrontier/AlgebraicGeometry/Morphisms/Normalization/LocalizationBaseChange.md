# Normalization along flat preimmersions

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Along a flat preimmersion, normalization commutes with base change once one normality condition is known.

- `isPullback_normalizationSchemeMap_of_flat_preimmersion` takes a flat preimmersion φ : X ⟶ Y and assumes that each quasi-compact open of Y has finitely many irreducible components. With `hnormal` asserting normality of the pullback of the normalization of Y to X, the theorem proves that the square formed by the induced map of normalizations and φ is cartesian. The finiteness condition on X under which the normalization of X is defined is supplied by `finite_irreducibleComponents_of_flat_preimmersion`.
- `mem_genericPoints_of_flat_preimmersion` shows that a point over a generic point is generic, and `isNormal_of_flat_preimmersion` transfers normality from the target via isomorphisms on stalks. The component finiteness lemma `finite_irreducibleComponents_of_mapsTo_injOn_genericPoints` applies to any map carrying generic points to generic points injectively, counting over a finite collection of target affine opens.

The general square follows by lifting through the normalization using preservation of generic points and then using uniqueness to check the inverse identities.

The hypothesis `hnormal` is not discharged in this file. The module docstring, and its title, also announce the application to the projection W ×_S Spec 𝒪_{S,s} ⟶ W for f : W ⟶ S and s in S, with the corresponding finiteness and normality statements; these are not in the file, and the section heading for them has nothing under it.

References are Stacks Project Tag 0307 for localization, Tag 035Q part (4) for the universal property, and Tag 07TD for the related base-change statement. The file also cites Tag 0BFU for normalized blowups and EGA IV 2.3.6(iii) for the component finiteness result in this special case.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.3.6 | `finite_irreducibleComponents_of_flat_preimmersion` | (iii), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/LocalizationBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 7 are kept. The 4 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.finite_irreducibleComponents_pullbackFst_fromSpecStalk`, `AlgebraicGeometry.flat_pullbackFst_fromSpecStalk`, `AlgebraicGeometry.isNormal_pullback_normalization_pullbackFst_fromSpecStalk`, `AlgebraicGeometry.isPullback_normalizationSchemeMap_pullbackFst_fromSpecStalk`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
