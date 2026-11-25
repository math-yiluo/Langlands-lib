# The Auslander–Buchsbaum formula

Module `StacksFrontier.RingTheory.ProjectiveDimension.AuslanderBuchsbaum`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a nonzero finite module M of finite projective dimension over a Noetherian local ring R, the projective dimension of M plus its depth at the maximal ideal equals the depth of R at that ideal.

`Module.projectiveDimension_add_depth_eq_depth_self` is the public formula, proved as `Stacks.ProjectiveDimension.DepthFormula.solution`. The depths in the equality are coerced from ℕ∞ into `WithBot ℕ∞`. The private helpers establish invariance of depth under linear equivalence, finiteness of depth for nonzero finite modules, and equality of the depths of R and a nonzero finite free module. They also give a minimal finite free cover whose kernel lies in the maximal ideal times the free module.

The proof inducts on projective dimension. One inequality uses the short exact sequence depth bound for a free cover and dimension shifting for its kernel. For the reverse inequality, the Ext characterization of depth and minimality of the cover make the map out of the kernel’s first nonvanishing Ext group zero, so the long exact sequence gives nonvanishing one degree earlier for M.

The formula requires `Nontrivial M` and `hM`, the condition that projective dimension is finite. It also carries `Small.{v} R` for a module in universe v, providing the enough-projectives instance in `ModuleCat.{v} R`. The comments explain why smallness follows mathematically from the other hypotheses.

The formula is Tag 090V. The proof uses the short exact sequence estimate of Tag 00LX and the Ext criterion associated with Tag 090R. The comments cite Tag 00MT and Tag 00N1 for the source’s proof via minimal resolutions and minors. They reference Tag 00LI for depth and Tag 00O4, Tag 00O5 and Tag 0CXC for projective dimension and resolutions. The table of references below records EGA 0 16.4.4, EGA 0 17.3.4 and SGA 2 III 2.2, SGA 2 III 2.4 and SGA 2 III 3.4.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [090V](https://stacks.math.columbia.edu/tag/090V) | `projectiveDimension_add_depth_eq_depth_self` | Stated with the sum on the left, in `WithBot ℕ∞`, for `Module.projectiveDimension` (Tag 00O4) and `Module.depth` along the maximal ideal (Tag 00LI). See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.4.4 | `le_depth_iff_forall_subsingleton_ext` | n ≤ depth iff Ext^i(k |
| SGA | 2 III 2.2 | `le_depth_iff_forall_subsingleton_ext` | special case |
| SGA | 2 III 2.4 | `le_depth_iff_forall_subsingleton_ext` | (3)⇔(4) |
| SGA | 2 III 3.4 | `le_depth_iff_forall_subsingleton_ext` | (1)⇔(3), special case |
| EGA | 0 17.3.4 | `projectiveDimension_add_depth_eq_depth_self` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/ProjectiveDimension/AuslanderBuchsbaum.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
