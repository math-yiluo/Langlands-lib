# Projective dimension of a module

Module `StacksFrontier.Algebra.Homology.ProjectiveDimension.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file names the projective dimension of a module over a ring, as a value in `WithBot ℕ∞`.

## Main definition

`Module.projectiveDimension R M`, for a ring `R` and an `R`-module `M`, is Mathlib's `CategoryTheory.projectiveDimension` of `ModuleCat.of R M`: the least `d` such that `Extⁱ(M, -)` vanishes for all `i > d`. It is an abbreviation, so Mathlib's lemmas on projective dimension apply directly.

## Watch for

- The definition is by `Ext` vanishing, not by the least length of a finite projective resolution. The comparison is proved elsewhere and needs `R` small in the universe of `M`.
- The zero module has projective dimension `⊥` here, not `0`. Bounds `≤ d` agree with the resolution-length definition, but an equality `= d` excludes the zero module.
- Only `Ring R` is assumed; commutativity is not needed.

## References

- Tag 00O4; More on Algebra, Example 0A5Q; a place in EGA in the table of references below.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00O4](https://stacks.math.columbia.edu/tag/00O4) | `Module.projectiveDimension` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 17.2.1 | `Module.projectiveDimension` | dim.proj definition |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/ProjectiveDimension/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
