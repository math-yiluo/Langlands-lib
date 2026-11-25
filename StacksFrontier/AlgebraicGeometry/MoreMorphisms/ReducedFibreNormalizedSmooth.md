# One finite extension making a normalized base change smooth at generic points of fibres

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizedSmooth`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a Nagata Dedekind domain with fraction field `K`, and `g : Y ⟶ Spec R` flat, quasi-compact and locally of finite type with `Y` normal, whose generic fibre has a dense open subscheme smooth over `K`. The file finds a finite extension `K₁/K` such that, with `B` the integral closure of `R` in `K₁`, the normalization of the base change `Y_B` of `Y` to `Spec B` is smooth over `Spec B` at every generic point of every fibre. This is the last paragraph of the proof of the reduced fibre theorem (Tag 09IL), for a scheme already in the shape its first paragraph produces.

## Main results

- `mem_smoothLocus_of_mem_genericPoints_fiber_of_dense_open_smooth`: for `g : Y ⟶ S` flat and locally of finite type over a locally Noetherian `S`, if the fibre over `s` has a dense open smooth over the residue field, every point generic in that fibre lies in the smooth locus.
- `universallyOpen_specMap_algebraMap_integralClosure`: for `R` Nagata Dedekind and `K₁/K` finite, `Spec (integralClosure R K₁) ⟶ Spec R` is universally open (flat and locally of finite presentation).
- `smoothAt_normalization_pullback_of_forall_isSolutionForStalk`: any finite `K₁/K` that is a solution (`IsSolutionForStalk`) at every bad point of `Y` — outside the smooth locus, generic in its fibre, over a nonzero prime — gives the smoothness conclusion.
- `exists_finiteExtension_smoothAt_normalization_pullback_of_dense_open_smooth`: such a `K₁` exists.

## Proofs

The extension comes from the simultaneous solution at all bad points proved in a companion file. For a point `y` of the normalized base change that is generic in its fibre, with image `w` in `Y_B`: if `w` is in the smooth locus of `Y_B ⟶ Spec B`, the normalization is an isomorphism there. Otherwise the point of `Y` below `w` lies outside the smooth locus of `g` (the smooth locus of a base change is the preimage of the smooth locus), is generic in its fibre by going down, and does not lie over the generic point because generic points of the generic fibre lie in the dense smooth open. The solution property then gives smoothness at `y`.

## Watch for

- This is not Tag 09IL itself: normality of `Y` and the dense smooth open in the generic fibre are hypotheses; the first paragraph, which supplies them, is in another file.
- Smoothness at a point is the library's `InfinitesimalLifting.SmoothAt`.
- The finiteness witness `hW` for the normalization is universally quantified in the conclusion.

## References

Tags 09IL, 02V4, 033C.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 15.5.5 | `universallyOpen_specMap_algebraMap_integralClosure` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreNormalizedSmooth.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
