# The normalization is smooth above the smooth locus

Module `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `q : W ⟶ S` be locally of finite presentation with `S` normal, and `ν` the normalization of `W` (with every quasi-compact open of `W` having finitely many irreducible components, hypothesis `hW`). The smooth locus of `q` is smooth over `S`, hence normal, so `ν` is an isomorphism over it.

- `InfinitesimalLifting.smoothAt_of_smooth_opens`: if `U.ι ≫ f` is smooth for an open `U`, then `f` is smooth at every point of `U`.
- `smooth_smoothLocus_ι_comp`: `q` restricted to its smooth locus is smooth.
- `Scheme.smoothAt_normalization_comp_of_mem_preimage_smoothLocus`: `ν ≫ q` is smooth (`InfinitesimalLifting.SmoothAt`) at every point of `ν⁻¹` of the smooth locus. `W` need not be reduced.

This is the first half of the last paragraph of the proof of the reduced fibre theorem (Tag 09IL): points over the smooth locus are handled directly; the remaining points, generic in fibres outside it, are treated in another file. It is not the full tag.

The file also cites Tag 033C.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 X 8.9 | `smooth_smoothLocus_ι_comp` | G' |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreSmoothLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
