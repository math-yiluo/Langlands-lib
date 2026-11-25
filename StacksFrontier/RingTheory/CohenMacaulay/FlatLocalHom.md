# Cohen–Macaulay rings and flat local maps

Module `StacksFrontier.RingTheory.CohenMacaulay.FlatLocalHom`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Depth and Krull dimension control when Cohen–Macaulayness ascends along a flat local homomorphism.

## Main results

- `Module.isMaximalCohenMacaulay_self_and_ringKrullDim_eq_of_flat` considers a flat local map R → S of Noetherian local rings with R Cohen–Macaulay. If S is finite as an R-module or dim S ≤ dim R, then S is Cohen–Macaulay and dim R = dim S.

For ascent, faithful flatness carries regular sequences to regular sequences, and depth is bounded by dimension. In the finite case, injectivity and integrality give the required bound on dim S.

The ascent theorem requires flatness in both branches of its disjunction. Two module docstrings of the file present the fibre criterion of Tag 045J, that S is Cohen–Macaulay exactly when R and the closed fibre S/𝔪_R S are, and list it as a main result; the file does not contain it.

## References

Tag 00R5 is the main statement. Tag 00LM concerns regular sequences under base change, Tag 00LK the bound of depth by dimension, and Tag 00OK integral extensions. See also EGA 0 17.3.5.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00R5](https://stacks.math.columbia.edu/tag/00R5) | `Module.isMaximalCohenMacaulay_self_and_ringKrullDim_eq_of_flat` | Cohen-Macaulayness of a Noetherian local ring `A` (Definition 00N8) is `Module.IsMaximalCohenMacaulay A A`, i.e. `depth_{𝔪_A}(A) = dim A`; the source's two alternatives are the disjunctive hypothesis `h` over the flatness common to both. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 17.3.5 | `Module.isMaximalCohenMacaulay_self_and_ringKrullDim_eq_of_flat` | (ii) necessity |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/FlatLocalHom.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 4 are kept. The 5 left out are not needed by the results for which the extract is made: `Module.isMaximalCohenMacaulay_self_iff_of_flat`, `Stacks.CohenMacaulay.FlatFibreCriterion.add_eq_add_iff_of_le_of_ne_top`, `Stacks.CohenMacaulay.FlatFibreCriterion.depth_maximalIdeal_le_of_supportDim_eq`, `Stacks.CohenMacaulay.FlatFibreCriterion.height_maximalIdeal_eq_height_add_height_map_maximalIdeal`, `Stacks.CohenMacaulay.FlatFibreCriterion.solution`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
