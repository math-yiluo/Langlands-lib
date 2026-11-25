# Local criteria for unramifiedness

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file connects the pointwise affine witnesses of unramifiedness with tests on whole affine charts and open covers.

`AlgebraicGeometry.unramified_tfae` gives four equivalent conditions for `f : X ⟶ S`.

1. The morphism `f` is unramified.
2. Every pair of affine opens `U ⊆ X` and `V ⊆ S` with `U ⊆ f⁻¹(V)` gives an algebra of sections satisfying `Algebra.Unramified`.
3. There is an open cover of `S` and an open cover of each preimage such that all the corresponding restricted morphisms `f.resLE` are unramified.
4. Such covers may be taken affine, with `Algebra.Unramified` tested on the maps of rings of sections.

The lemma `unramified_iff_affineLocally` matches the pointwise definition to Mathlib’s `affineLocally` construction for the ring-map predicate `Algebra.Unramified`. Its inputs are `unramified_ringHom_propertyIsLocal`, which says that this predicate is local, and `unramified_ringHom_stableUnderCompositionWithLocalizationAwaySource`, its stability under precomposition by a principal localization.

For the proofs, the ring-map predicate is expressed as the conjunction of formal unramifiedness with finite type, which is local; with the stability above, Mathlib’s affine-local machinery gives the chart and open-cover tests. A private lemma assembles a property local at the source and the target from an open cover of the target and open covers of the preimages.

The cover index types lie in the scheme universe.

The module docstring also announces G-unramified versions, restriction lemmas and `HasRingHomProperty` instances; they are not in this file.

References are Tag 02G6 for the four-way criterion.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02G6](https://stacks.math.columbia.edu/tag/02G6) | `unramified_tfae` | unramified characterization |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Unramified/Local.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 13 declarations of the source file 5 are kept. The 8 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.gUnramified_iff_affineLocally`, `AlgebraicGeometry.gUnramified_resLE`, `AlgebraicGeometry.gUnramified_ringHom_propertyIsLocal`, `AlgebraicGeometry.gUnramified_ringHom_stableUnderCompositionWithLocalizationAwaySource`, `AlgebraicGeometry.gUnramified_tfae`, `AlgebraicGeometry.hasRingHomProperty_gUnramified`, `AlgebraicGeometry.hasRingHomProperty_unramified`, `AlgebraicGeometry.unramified_resLE`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
