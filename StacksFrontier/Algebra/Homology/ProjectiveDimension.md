# Projective dimension by resolutions and syzygies

Module `StacksFrontier.Algebra.Homology.ProjectiveDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file relates Mathlib's projective dimension, defined by `Ext` vanishing, to resolutions by projectives and their syzygies, for an object of an abelian category.

## Main results

- `CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution`: for `X` in an abelian category with `HasProjectiveResolution X` and `d : ℕ`, these are equivalent: `HasProjectiveDimensionLE X d`; some resolution of `X` by projectives (the library's `ObjectProperty.LeftResolution`) has zero terms above degree `d`; the `d`-th syzygy (cycles of the augmented complex) of some such resolution is projective; that of every one is.
- `leftResolutionOfProjectiveResolution`: a Mathlib `ProjectiveResolution` read as a left resolution.
- Public helpers in the namespace `StacksDraft.ProjectiveDimension`: the augmentation `πZero F : P₀ ⟶ Y` of a projective resolution, an epimorphism and a cokernel of `d 1 0` (`d_comp_πZero`, `epi_πZero`, `exact₀'`); `quasiIsoAt_zero_of`; exactness of an augmented complex in degrees `1` and `n + 2` (`exactAt_augment_one`, `exactAt_augment_succ_succ`); exactness of `X → Y → Z` after precomposing with an epimorphism or postcomposing with a monomorphism (`exact_of_epi_comp`, `exact_of_comp_mono`).

The proof is dimension shifting along short exact sequences with projective middle term.

## Watch for

- No declaration here carries Tag 065S; a docstring of the file and the table of tags below attribute it to Mathlib lemmas.
- The docstrings of the file also describe Schanuel's lemma, a module of infinite projective dimension over the dual numbers, the projectivity of the last syzygy of a truncated resolution, and localization of bounds on projective and global dimension. None of these is declared in the file.

## References

Tag 0CXC, with Tags 00LQ, 00O4, 00O5, 00O7, 0CXD, 0CXE, 0CXF, 065R and 0A5Q named in its discussion; Tag 065S; places in EGA in the table of references below.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0CXC](https://stacks.math.columbia.edu/tag/0CXC) | `CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution` | A resolution `⋯ → P₁ → P₀ → M → 0` is an `ObjectProperty.LeftResolution` by the class of projective objects (00LQ), the notion 00O7 uses; the source's `M`, `Ker(P₀ → M)` and `Ker(P_{d-1} → P_{d-2})` are the single syzygy `(F.complex.toSingle₀AsComplex X F.π).cycles d`, the `d`-th cycles of the augmentation `F.π` read as a complex; see the module docstring. |
| [065S](https://stacks.math.columbia.edu/tag/065S) | `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁` | (1) |
| [065S](https://stacks.math.columbia.edu/tag/065S) | `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂` | (2) |
| [065S](https://stacks.math.columbia.edu/tag/065S) | `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃` | (3) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 17.2.1 | `projective_cycles_iff` | more general |
| EGA | 0 17.2.1 | `exists_projectiveResolution_isZero` | partial |
| EGA | 0 17.2.1 | `CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution` | dim.proj resolution char |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/ProjectiveDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 66 declarations of the source file 38 are kept. The 28 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 10 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text; the 3 on declarations kept here are listed above.
