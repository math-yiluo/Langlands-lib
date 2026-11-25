# Depth along an ideal

Module `StacksFrontier.RingTheory.Depth.Defs.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file defines the library’s ideal-relative depth for any module M over a commutative ring R.

`Module.stacksDepth R I M` is ∞ when IM = M and otherwise the supremum in ℕ∞ of lengths of M-regular lists in I. `Module.depthSup` always takes the raw supremum (`Module.depthSup_eq_iSup` restates it as an indexed supremum). Regularity requires injectivity on each successive quotient and a nonzero final quotient.

`Module.depth_eq_depth_of_linearEquiv` gives invariance of the I-depth under R-linear equivalences. `isRegular_take` passes regularity to prefixes, and `Module.le_depth_of_isRegular` bounds the length of an M-regular list in I by the I-depth.

The two definitions agree when IM ≠ M. For the zero module, `Module.depth_eq_top_of_subsingleton` gives infinite depth, while the raw supremum is zero. The module docstring uses the unprefixed name of the depth and announces a result on depth along the zero ideal that is not in this file.

References include Tag 00LI, EGA 0 16.4.5, EGA IV 5.7.1, EGA IV 6.10.3, SGA 2 III 2.8, SGA 2 IV 5.3, and SGA 2 XI 3.10.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00LI](https://stacks.math.columbia.edu/tag/00LI) | `Module.stacksDepth` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.4.5 | `Module.stacksDepth` | more general |
| EGA | IV 5.7.1 | `Module.stacksDepth` | more general |
| EGA | IV 6.10.3 | `Module.stacksDepth` |  |
| SGA | 2 III 2.8 | `Module.stacksDepth` | special case |
| SGA | 2 IV 5.3 | `Module.stacksDepth` |  |
| SGA | 2 XI 3.10 | `Module.stacksDepth` |  |
| EGA | 0 16.4.5 | `Module.depth_eq_top_of_subsingleton` | partial |
| EGA | 0 16.4.5 | `Module.depthSup` | partial |
| EGA | IV 6.10.3 | `Module.depthSup` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/Defs/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 7 are kept. The 2 left out are not needed by the results for which the extract is made: `Module.depth_bot_eq_zero`, `Module.le_depthSup`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `Module.depth` is `Module.stacksDepth` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 9 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
