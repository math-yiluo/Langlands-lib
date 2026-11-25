# Unramified morphisms as formally unramified morphisms locally of finite type

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file characterizes unramified morphisms by formal unramifiedness and a finiteness condition.

`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_formallyUnramified` says that `f : X ⟶ S` is unramified if and only if it is locally of finite type and formally unramified, in the sense of Mathlib’s `LocallyOfFiniteType` and `FormallyUnramified`.

The proof starts from the affine-chart condition of `unramified_tfae` and reads both Mathlib properties as conditions on all `appLE` maps. One private lemma splits `Algebra.Unramified` of a ring map into finite type and formal unramifiedness; another splits a condition on all `appLE` maps along such a conjunction.

The module docstring also announces a G-unramified analogue, permanence results and consequences at points; they are not in this file.

References are Tag 02HE (unramified case) and EGA IV 17.4.1, 17.4.1.2 and 17.4.2.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [02HE](https://stacks.math.columbia.edu/tag/02HE) | `unramified_iff_locallyOfFiniteType_and_formallyUnramified` | unramified case |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 17.4.1.2 | `unramified_iff_locallyOfFiniteType_and_formallyUnramified` | a) formally unramified |
| EGA | IV 17.4.2 | `unramified_iff_locallyOfFiniteType_and_formallyUnramified` | a) ⇔ e) |
| EGA | IV 17.4.1 | `unramified_iff_locallyOfFiniteType_and_formallyUnramified` | a) <=> e) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Unramified/Properties.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 17 declarations of the source file 3 are kept. The 14 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
