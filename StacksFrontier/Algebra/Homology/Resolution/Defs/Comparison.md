# Left resolutions by a class of objects

Module `StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file sets up the notion of a left resolution `… → F₁ → F₀ → Z → 0` whose terms lie in a given class of objects of a category. As in Mathlib's `CategoryTheory.ProjectiveResolution`, a resolution is an `ℕ`-indexed chain complex `F` together with a quasi-isomorphism `π : F ⟶ Z[0]` to the complex with `Z` in degree 0.

## Definitions

- `CategoryTheory.ObjectProperty.LeftResolution P Z`: in a category with a zero object and zero morphisms, a chain complex whose terms satisfy `P`, with homology in every degree, and a quasi-isomorphism `π` to `Z` in degree 0.
- `LeftResolution.toProjectiveResolution`: given a proof that every term is projective, the same data as a Mathlib `ProjectiveResolution Z`.

## Watch for

- `LeftResolution` is the library's own structure; its fields `hasHomology` and `quasiIso` are registered as instances.
- The module docstring also describes resolutions of modules, by free and by finite free modules, and two results on them, which the file does not contain.

## References

Tag 00LQ (for `LeftResolution`).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00LQ](https://stacks.math.columbia.edu/tag/00LQ) | `LeftResolution` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/Resolution/Defs/Comparison.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 28 declarations of the source file 9 are kept. The 19 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 2 references to EGA and SGA that the source writes as attributes of that library were on declarations left out; none is listed above.
