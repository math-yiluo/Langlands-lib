# A Krull dimension bound for projective dimension

Module `StacksFrontier.RingTheory.ProjectiveDimension.KrullDimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A finite module of finite projective dimension over a Noetherian local ring has projective dimension at most the Krull dimension of the ring. The result applies to the residue field whenever its projective dimension is finite.

`Module.projectiveDimension_le_ringKrullDim`, proved as `Stacks.ProjectiveDimension.KrullBound.solution`, states this for a finite module M over a commutative Noetherian local ring R. The hypothesis `hM` excludes the value ⊤ for projective dimension.

For a nonzero M, the Auslander–Buchsbaum formula bounds projective dimension by the depth of R at its maximal ideal. The depth bound by support dimension, applied to R as its own module, then gives the desired inequality. The proof treats the zero module separately, using its projective dimension ⊥.

The Lean statement requires `Small.{v} R`, where M lives in universe v. This permits the computation of projective dimension using resolutions within M’s universe. The inequality is in `WithBot ℕ∞`. Tag 00OB is stated for the residue field in the Stacks Project, and the Lean result covers every finite module under the stated hypotheses.

The proof uses Tag 090V for Auslander–Buchsbaum and Tag 00LK for the depth bound. The comments cite Tag 0CXF, Tag 00MT and Tag 00N1 for the source’s minimal-resolution argument and Tag 00LX and Tag 090R as inputs to the formula. They reference Tag 00O4, Tag 00O5 and Tag 0CXC for projective dimension and resolutions, and relate the residue-field bound to Tag 00OA and the regularity criterion in Tag 00OC.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00OB](https://stacks.math.columbia.edu/tag/00OB) | `projectiveDimension_le_ringKrullDim` | Stated for an arbitrary finite module `M` rather than only for `κ`, the source's proof using nothing else; `pd_R M` is `Module.projectiveDimension` (Tag 00O4) and finiteness of it is `≠ ⊤`. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/ProjectiveDimension/KrullDimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
