# Finite free resolutions over local rings

Module `StacksFrontier.RingTheory.LocalRing.ProjectiveDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a commutative local Noetherian ring R, a bound d on the projective dimension of a finite module M is equivalent to the existence of a resolution of length at most d by finite free modules.

- `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free_finite` identifies `HasProjectiveDimensionLE M d` with the existence of a left resolution of M by finitely generated free modules whose terms are zero above degree d, under `IsNoetherianRing R` and `Module.Finite R M`. It is proved as `Stacks.LocalRing.FiniteFreeResolution.solution`.

The proof rewrites the allowed class of resolving modules in the criterion by finite projective resolutions, `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite` from `StacksFrontier.Algebra.Homology.ProjectiveDimension.FiniteResolution`. Over a local ring the projective objects of `ModuleCat R` are exactly the free modules: a free module is projective, and Kaplansky's theorem `Module.free_of_projective_of_isLocalRing` gives freeness from projectivity. The rewrite retains finite generation on both sides.

The statement uses `Small.{v} R` for modules in `ModuleCat.{v} R`. A left resolution here is a nonnegatively indexed chain complex augmented by a quasi-isomorphism to M in degree zero. The term in degree d may be zero. The tagged lemma compares the new condition (7) with the projective-dimension bound in item 1 of the equivalence of Tag 0CXC. The first module docstring of the file describes the corresponding statement for free resolutions of arbitrary modules (Tag 0CXD), which is not in the file.

The new condition is Tag 0CXF. The finite projective-resolution criterion is Tag 0CXE, Kaplansky’s theorem is Tag 0593, with the finite case at Tag 00NX, and left resolutions are referenced at Tag 00LQ and Tag 00O7. The table of references below also cites EGA 0 17.2.1 and EGA 0 17.2.2, and SGA 3 VIA 2.1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0CXF](https://stacks.math.columbia.edu/tag/0CXF) | `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free_finite` | Condition (7) is added to Lemmas 0CXC, 0CXD and 0CXE by stating its equivalence with item 1 of 0CXC's `TFAE`. A resolution `0 → F_d → ⋯ → F₀ → M → 0` by finite frees is an `ObjectProperty.LeftResolution` for the class of finite free modules (00LQ), the notion 00O7 uses, vanishing in degrees `> d`; see the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIA 2.1.3 | `isProjective_eq_free` | more general |
| EGA | 0 17.2.2 | `projective_and_eq_free_and` | more general |
| SGA | 3 VIA 2.1.3 | `projective_and_eq_free_and` | more general |
| EGA | 0 17.2.1 | `solution` | partial |
| EGA | 0 17.2.2 | `solution` |  |
| EGA | 0 17.2.2 | `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free_finite` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/LocalRing/ProjectiveDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 4 are kept. The 2 left out are not needed by the results for which the extract is made: `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_free`, `Stacks.LocalRing.ProjectiveIsFree.solution`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
