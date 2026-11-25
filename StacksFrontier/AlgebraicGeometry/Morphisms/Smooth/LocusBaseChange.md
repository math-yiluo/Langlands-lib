# Smooth loci under flatness in a base change square

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In a cartesian square, the smooth locus of a base-changed morphism is the inverse image of the original smooth locus when the original morphism or the base change map is flat.

`Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` takes f : X ⟶ S locally of finite presentation and a base change along g : S′ ⟶ S. With f′ : X′ ⟶ S′ and projection g′ : X′ ⟶ X, it equates `f'.smoothLocus` with the inverse image of `f.smoothLocus` under g′. The hypothesis `hflat` is the disjunction `Flat f ∨ Flat g`.

The proof chooses compatible affine neighborhoods of the images of a point of X′. Their inverse-image intersection in X′ is affine, and the rings of sections form a pushout. Via `formallySmooth_stalkMap_iff`, membership in each smooth locus becomes smoothness at the corresponding prime. The comparison then follows from `Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout_of_flat`.

The statement takes `LocallyOfFinitePresentation f'` as an instance to form the smooth locus of f′. This instance is available by base-change stability from f and the cartesian square. The flatness disjunction covers the two cases of the cited Stacks result.

Stacks Project, Tag 02V4. EGA IV 17.7.1, IV 17.7.2 and IV 17.7.4. SGA 1 II 4.13 and SGA 3 VIB 2.5, VIB 3.10 and X 8.9.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02V4](https://stacks.math.columbia.edu/tag/02V4) | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.7.2 | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` | (ii) |
| EGA | IV 17.7.4 | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` | (v) |
| EGA | IV 17.7.1 | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` | (ii) smooth |
| SGA | 1 II 4.13 | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` | special case |
| SGA | 3 VIB 2.5 | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` | special case |
| SGA | 3 VIB 3.10 | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` | special case |
| SGA | 3 X 8.9 | `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Smooth/LocusBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 7 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
