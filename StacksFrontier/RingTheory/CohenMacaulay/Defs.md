# Cohen–Macaulay modules and rings

Module `StacksFrontier.RingTheory.CohenMacaulay.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The definitions express Cohen–Macaulay conditions as equalities between depth and dimension. They distinguish the dimension of a module's support from the dimension of the whole ring and give local and global versions.

- For a module over a commutative local ring, `Module.IsMaximalCohenMacaulay` equates depth at the maximal ideal with the ring's Krull dimension. `Module.IsCohenMacaulayAtMaximalIdeal` equates the same depth with the dimension of the module's support.
- `IsCohenMacaulayModule` is a predicate for finite modules over a Noetherian local ring, comparing `Module.depthSup` with the Krull dimension of the support. `IsCohenMacaulayLocalRing` applies that predicate to the ring as a module over itself.
- `localRingDepth` is the supremum of lengths of regular sequences in the maximal ideal of a commutative local ring. `IsCohenMacaulayLocalRingPropForm` requires a Noetherian local ring to have this depth equal to its Krull dimension. `IsCohenMacaulayRing` imposes this condition on the localization of a Noetherian ring at every prime.

The lemma `isCohenMacaulayLocalRing_iff_isCohenMacaulayModule_self` simply unfolds the definition of `IsCohenMacaulayLocalRing`.

The two predicates in the `Module` namespace allow arbitrary modules and can be formed over non-Noetherian rings. Depth comparisons take place in `WithBot ℕ∞`, where the dimension of empty support is bottom, while the zero module has infinite `Module.stacksDepth`. The module docstring also lists, and discusses, a definition of Cohen–Macaulay modules over a ring that need not be local (Tag 0AAH), which the file does not contain; the note of Tag 00N3 below still refers to it.

## References

Tag 00N3, Tag 00N8, Tag 00NC, Tag 00NF and Tag 00LI. EGA 0 16.4.5, 16.5.1 and 16.5.13, EGA IV 5.7.1 and 7.5.3, and SGA 2 III 2.8.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00NF](https://stacks.math.columbia.edu/tag/00NF) | `Module.IsMaximalCohenMacaulay` | Stated without the Noetherian and finiteness hypotheses, which the lemmas assume \   where needed; under them this is the source's condition, with the depth of Tag 00LI. See the \   module docstring. |
| [00N3](https://stacks.math.columbia.edu/tag/00N3) | `Module.IsCohenMacaulayAtMaximalIdeal` | Stated without the Noetherian and finiteness hypotheses, as in tags 00LI, 00NF \   and 0AAH; the equation is oriented `depth_𝔪(M) = dim Supp(M)`, the spelling of \   Cohen–Macaulayness already used by tags 00LK, 00NF, 0AAG, 0AAH and 0C6G. The name records \   that the depth is taken at the maximal ideal, `Module.IsCohenMacaulay` being Definition 0AAH \   for a not necessarily local ring. See the module docstring. |
| [00N8](https://stacks.math.columbia.edu/tag/00N8) | `IsCohenMacaulayLocalRing` |  |
| [00NC](https://stacks.math.columbia.edu/tag/00NC) | `IsCohenMacaulayRing` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 7.5.3 | `Module.IsMaximalCohenMacaulay` |  |
| EGA | 0 16.5.1 | `Module.IsCohenMacaulayAtMaximalIdeal` | CM module def |
| EGA | IV 7.5.3 | `Module.IsCohenMacaulayAtMaximalIdeal` |  |
| EGA | 0 16.5.1 | `IsCohenMacaulayModule` | CM module def |
| EGA | IV 5.7.1 | `IsCohenMacaulayModule` | F is Cohen–Macaulay at x |
| EGA | IV 7.5.3 | `IsCohenMacaulayModule` |  |
| EGA | 0 16.5.13 | `IsCohenMacaulayLocalRing` | local ring |
| EGA | 0 16.5.1 | `IsCohenMacaulayLocalRing` |  |
| EGA | IV 5.7.1 | `IsCohenMacaulayLocalRing` |  |
| EGA | IV 7.5.3 | `IsCohenMacaulayLocalRing` |  |
| EGA | 0 16.4.5 | `localRingDepth` | special case |
| SGA | 2 III 2.8 | `localRingDepth` | special case |
| EGA | 0 16.5.1 | `IsCohenMacaulayLocalRingPropForm` |  |
| EGA | IV 5.7.1 | `IsCohenMacaulayLocalRingPropForm` |  |
| EGA | IV 7.5.3 | `IsCohenMacaulayLocalRingPropForm` |  |
| EGA | 0 16.5.13 | `IsCohenMacaulayRing` |  |
| EGA | IV 7.5.3 | `IsCohenMacaulayRing` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 8 are kept. The 2 left out are not needed by the results for which the extract is made: `Module.IsCohenMacaulay`, `isCohenMacaulayRing_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 17 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
