# Descent of finite presentation along a faithfully flat map

Module `StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file descends finite presentation of modules through faithfully flat maps of commutative rings.

`Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat` takes a faithfully flat `R`-algebra `S`, an `R`-module `M` and a map `f : M →ₗ[R] N` exhibiting the `S`-module `N` as the base change of `M` (`IsBaseChange S f`). If `N` is finitely presented over `S`, then `M` is finitely presented over `R`.

The proof gets finiteness of `M` from Mathlib's descent of finite generation and writes `M` as a quotient of a finite free module. The private lemma `fg_ker_of_faithfullyFlat` shows that the kernel is finitely generated: by flatness its base change is the kernel of a surjection onto the finitely presented module `S ⊗ M`, hence finite, and finite generation descends.

## Scope and references

Tag 03C4 is represented by part (2). Mathlib supplies the accompanying descent of finite generation and flatness. For finite presentation of algebras a comment of the file cites Mathlib's `Algebra.FinitePresentation.baseChange` and `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` (Tag 00QQ). The module docstring still describes the descent of projectivity, countable generation, finite type, Noetherianity and reducedness, finite models over the base of a localization, and an isomorphism criterion modulo nilpotent ideals, with their tags; none of these is in the file, and its remaining sections are empty. The table of references below records the EGA and SGA citations.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [03C4](https://stacks.math.columbia.edu/tag/03C4) | `FinitePresentation.of_isBaseChange_of_faithfullyFlat` | Part (2). Part (1) is `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and part (3) is `Module.Flat.of_flat_tensorProduct`, both in Mathlib. |
| [00QQ](https://stacks.math.columbia.edu/tag/00QQ) | `Algebra.FinitePresentation.baseChange` | a base change of an algebra of finite presentation is of finite presentation |
| [00QQ](https://stacks.math.columbia.edu/tag/00QQ) | `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` | finite presentation descends along a faithfully flat base change |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.5.3 | `fg_ker_of_faithfullyFlat` | special case |
| EGA | IV 2.5.2 | `FinitePresentation.of_isBaseChange_of_faithfullyFlat` | (ii), descent, affine |
| EGA | IV 2.5.3 | `FinitePresentation.of_isBaseChange_of_faithfullyFlat` | fin. pres., descent |
| SGA | 1 VIII 1.11 | `FinitePresentation.of_isBaseChange_of_faithfullyFlat` | fin. pres., descent |
| SGA | 1 VIII 1.10 | `FinitePresentation.of_isBaseChange_of_faithfullyFlat` | fin. pres., affine |
| SGA | 4½ Arcata 1.4.2 | `FinitePresentation.of_isBaseChange_of_faithfullyFlat` | (ii), fin. presentation |
| SGA | 1 VIII 3.6 | `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` | affine case |
| SGA | 3 VIB 10.8 | `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` | special case |
| SGA | 3 XIX 2.1 | `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` | special case |
| SGA | 6 VIII 1.6 | `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` | special case |
| EGA | IV 2.7.1 | `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` | special case |
| EGA | IV 2.7.1.1 | `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/FaithfullyFlat/Descent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 30 declarations of the source file 2 are kept. The 28 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 12 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
