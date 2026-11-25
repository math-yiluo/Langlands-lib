# Finite presentation descends along fpqc coverings

Module `StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A quasi-coherent module on a scheme is of finite presentation as soon as its pullback to every member of an fpqc covering is. This file proves this, together with general criteria for finite presentation of sheaves of modules from local data.

## Main results

- `isFinitePresentation_of_pullback_fpqcCover`: let M be a quasi-coherent module on a scheme X and 𝒰 a cover of X for `Scheme.fpqcPrecoverage`. If the pullback of M along every member of 𝒰 is of finite presentation, so is M.
- `isFinitePresentation_of_coversTop`: on a site, a sheaf of modules is of finite presentation if its restrictions to the members of a family covering the final object (`J.CoversTop`) are; the category must have binary products, and the site must satisfy weak sheafification and local-bijectivity hypotheses for abelian groups, also on its slice sites.
- `over_has_finite_global_presentation`, `over_isFinitePresentation_of_finite_global`: a finite global presentation of the restriction of a module to an open U gives a finite presentation of the module on the slice over U.

## Proofs

The question is local on X, so it reduces to an affine base, using a private criterion that finite presentation can be checked on an affine open cover (built from the criteria above and the fact that a finitely presented quasi-coherent module on an affine scheme has a finite global presentation). Over an affine base the fpqc covering is refined by finitely many affine schemes flat over the base; their coproduct maps to the base by a flat surjective morphism of affine schemes, which is faithfully flat on global sections. There the module is the sheaf associated with its global sections, and finite presentation of modules descends along a faithfully flat ring map.

## Points to watch

- M must be quasi-coherent; finite presentation is Mathlib's `SheafOfModules.IsFinitePresentation`, and pullback is `Scheme.Modules.pullback`.
- The cover may be indexed in another universe v; all schemes lie in universe u.

## References

Tag 05B0. The table of references below attaches places in EGA IV and SGA 1 and in SGA 4½ to the main theorem and to several private steps, some of them as special or partial cases.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [05B0](https://stacks.math.columbia.edu/tag/05B0) | `isFinitePresentation_of_pullback_fpqcCover` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.5.3 | `tilde_isFinitePresentation_of_faithfullyFlat_baseChange` | partial |
| SGA | 4½ Arcata 1.4.2 | `tilde_isFinitePresentation_of_faithfullyFlat_baseChange` |  |
| EGA | IV 2.5.2 | `isFinitePresentation_of_affine_flat_surjective` | (ii), special case |
| SGA | 1 VIII 1.10 | `isFinitePresentation_of_affine_flat_surjective` | special case |
| EGA | IV 2.5.2 | `isFinitePresentation_of_fpqcCover_affine` | (ii), special case |
| SGA | 1 VIII 1.10 | `isFinitePresentation_of_fpqcCover_affine` | special case |
| SGA | 1 VIII 1.10 | `isFinitePresentation_of_pullback_fpqcCover` | finite presentation |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Descent/Modules/FpqcFinitePresentation.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 7 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
