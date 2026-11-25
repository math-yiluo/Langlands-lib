# Regular sequences, depth, and associated primes

Module `StacksFrontier.RingTheory.Depth.Criteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file computes depth along an ideal using weakly regular sequences, describes how depth changes on quotienting by a nonzerodivisor, and bounds local depth by dimensions of associated prime quotients.

## Results

- `Module.depth_eq_iSup_isWeaklyRegular_length` identifies the I-depth of a finite module M over a commutative ring R with the supremum of the lengths of weakly M-regular sequences in I. Each element acts injectively on the quotient by its predecessors.
- `Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append` treats finite modules over a Noetherian ring. For a nonzerodivisor x on M in I, the I-depth of M/xM plus one equals the I-depth of M. If IM ≠ M, any M-regular list in I can be extended by a list in I to one of length exactly the depth.
- `Module.stacks_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` bounds the maximal-ideal depth of a finite module over a Noetherian local ring by dim(R/𝔭) for each 𝔭 associated to M.

## Proofs and hypotheses

For the supremum formula, IM ≠ M ensures that each final quotient is nonzero. When IM = M, Nakayama’s lemma supplies an element of I acting identically, so repetition gives weakly regular lists of all lengths. Prepending x and applying the depth inequality for the multiplication short exact sequence give the two bounds for the quotient formula. Localization at a maximal ideal containing I and the annihilator gives finiteness of depth when IM ≠ M, so iteration extends regular lists to the required length. The associated prime bound inducts on length. For a nonzerodivisor x in the maximal ideal, a prime minimal over 𝔭 + (x) is strictly larger than 𝔭 and is associated to a quotient by a suitable power of x, of depth one less.

The quotient and extension results allow any ideal of a Noetherian ring. Only the extension requires IM ≠ M. The quotient equality is an equality in ℕ∞, with both sides infinite when IM = M. The associated prime inequality concerns maximal-ideal depth and uses `WithBot ℕ∞` for the dimension comparison. The module docstrings write the depth and this inequality without the `stacks` prefix of their names.

References include Tag 0AUI, Tag 090R, Tag 0BK4, EGA 0 16.4.5, EGA 0 16.5.9, EGA 0 16.4.6 (iii), first inequality, and SGA 2 III 2.6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0AUI](https://stacks.math.columbia.edu/tag/0AUI) | `depth_eq_iSup_isWeaklyRegular_length` |  |
| [090R](https://stacks.math.columbia.edu/tag/090R) | `depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append` | Stated for an arbitrary ideal of a Noetherian ring; `M` nonzero is used only as \   `I • M ≠ M`, and only by part (2), so both parameters are bound inside the conclusion. |
| [0BK4](https://stacks.math.columbia.edu/tag/0BK4) | `stacks_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.4.5 | `depth_eq_iSup_isWeaklyRegular_length` | more general |
| SGA | 2 III 2.6 | `depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append` |  |
| EGA | 0 16.5.9 | `exists_isRegular_length_eq_depth` | special case |
| SGA | 2 III 2.6 | `exists_isRegular_length_eq_depth` | special case |
| EGA | 0 16.4.6 | `stacks_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` | (iii), first inequality |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Depth/Criteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 31 declarations of the source file 30 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Depth.ModNonzerodivisor.depth_maximalIdeal_le_depth_localizedModule_maximalIdeal`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` is `Module.stacks_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` here.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
