# Finite free complexes with a maximal Cohen–Macaulay syzygy

Module `StacksFrontier.RingTheory.CohenMacaulay.FreeComplex`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Successive finite free covers of a module over a Cohen–Macaulay local ring produce a finite exact complex whose leftmost term has maximal depth.

## Main result

`Module.IsMaximalCohenMacaulay.exists_composableArrows_exact_free_and_isMaximalCohenMacaulay_left` assumes a Noetherian local Cohen–Macaulay ring R of dimension d and a finite R-module M of depth e, with d and e given as natural numbers. It constructs an exact complex from 0 through K, d − e finite free terms, and M to 0. The finite leftmost module K is maximal Cohen–Macaulay, so its depth equals dim R.

The proof repeatedly splices in a short exact sequence from a finite free cover of the current leftmost module. Each new syzygy either has greater depth or is already maximal Cohen–Macaulay. The cover includes an extra free summand mapping to zero to ensure its kernel is nonzero, so the depth bound for nonzero finite modules applies.

The natural-number depth assumption forces M to be nonzero. When d = e, the construction uses the identity map of M with no intermediate free terms. The theorem uses `CategoryTheory.ComposableArrows` in `ModuleCat.{u} R` for `R : Type u`. The first map is monic and the last epic, expressing exactness at the ends, and the rightmost object is M itself.

## References

Tag 00NG is the existence statement. The syzygy depth step uses Tag 00NE, and the depth bound uses Tag 00LK. The depth-bound lemmas record a special case of EGA IV 5.7.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00NG](https://stacks.math.columbia.edu/tag/00NG) | `exists_composableArrows_exact_free_and_isMaximalCohenMacaulay_left` | Cohen-Macaulayness of the Noetherian local ring `R` is `Module.IsMaximalCohenMacaulay R R`, i.e. `depth_𝔪(R) = dim R` (Definition 00N8); the complex is a `ComposableArrows (ModuleCat R) (d - e + 1)` whose rightmost object is `M`, its interior exactness being `Exact` and the outer two conditions `Mono` and `Epi` as in `ShortComplex.ShortExact`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.7.3 | `coe_depth_le_ringKrullDim` | special case |
| EGA | IV 5.7.3 | `depth_le_of_ringKrullDim_eq` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/FreeComplex.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
