# Existence of finite free resolutions

Module `StacksFrontier.Algebra.Homology.Resolution.Existence`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves that a finite module over a noetherian commutative ring has a resolution by finite free modules. Resolutions are encoded elementarily, with linear maps between types, not as Mathlib chain complexes.

## Definitions and results

- `FreeResolutionData R M`: for a commutative ring `R` and an `R`-module `M`, a family of `R`-modules `F n` (in the universe of `M`), differentials `d n : F (n+1) →ₗ F n` and an augmentation `ε : F 0 →ₗ M`.
- Predicates on such data: `IsComplex` (consecutive composites vanish), `IsExact` (`ε` surjective, `range (d 0) = ker ε`, `range (d (n+1)) = ker (d n)`), `IsFinite`, `IsFiniteFree`.
- `exists_finite_free_resolution`: if `R` is noetherian and `M` is finite, there are data that are exact with every term free and finitely generated.

## Proof

The namespace `FreeResolutionConstruction` iterates a covering step: a finite module `K` is covered by some `Fin n → R`, then the kernel of the cover, finite by noetherianity, is covered, and so on; the differentials are the covers followed by the inclusions of the kernels, and exactness is read off from their images and kernels. The namespace also has the layers for arbitrary modules, each covered by the free module `K →₀ R` (`Layer`, `coverLayer`, `nextLayer`, `layers`); no resolution is assembled from them in this file.

## Watch for

- `M` must lie in the same universe as `R`.
- `IsComplex` is defined but used nowhere; the theorem asserts `IsExact`, which has no separate complex condition.
- `FreeResolutionData` is the file's own notion, not a Mathlib chain complex.
- The module docstring also announces a free resolution of every module, which the file does not contain.

## References

Tag 00LP, part (2), for `exists_finite_free_resolution`. The table of references below gives places in EGA and SGA.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00LP](https://stacks.math.columbia.edu/tag/00LP) | `exists_finite_free_resolution` | (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.1.10 | `IsExact` |  |
| EGA | 0 11.9.2 | `exists_finite_free_resolution` | special case |
| EGA | IV 12.3.2 | `exists_finite_free_resolution` | (i), special case |
| SGA | 2 VIII 1.2 | `exists_finite_free_resolution` | partial |
| SGA | 4 IX 2.3 | `exists_finite_free_resolution` | partial |
| SGA | 6 VI 1.6 | `exists_finite_free_resolution` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/Resolution/Existence.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 59 declarations of the source file 51 are kept. The 8 left out are not needed by the results for which the extract is made: `FreeResolutionConstruction.buildResolution`, `FreeResolutionConstruction.buildResolution_isExact`, `FreeResolutionConstruction.buildResolution_isFree`, `FreeResolutionConstruction.dd`, `FreeResolutionConstruction.dd_ker`, `FreeResolutionConstruction.dd_range`, `FreeResolutionData.IsFree`, `exists_free_resolution`.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
