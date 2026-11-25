# Generators and quotients of regular local rings

Module `StacksFrontier.RingTheory.RegularLocalRing.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Minimal generators of a regular local ring’s maximal ideal form a regular sequence and control its successive quotients. The file also proves that a regular local ring is a domain, and compares the minimal numbers of generators of maximal ideals along a surjection of local rings.

## Main results

- `IsRegularLocalRing.stacks_isDomain` gives the domain property by invoking `isDomain_of_isRegularLocalRing_aux`. It is a theorem, not an instance.
- `IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay`, proved as `Stacks.RegularLocalRing.RegularSequence.solution`, shows that every minimal generating list of the maximal ideal 𝔪 of a regular local ring R is a regular sequence. Quotienting by a prefix of length c gives a regular local ring of dimension dim R − c. The theorem also gives `Module.IsMaximalCohenMacaulay R R`, the equality of self-depth at 𝔪 and dimension.
- `Stacks.RegularLocalRing.SpanFinrank.spanFinrank_maximalIdeal_succ_le_of_surjective` takes a surjection π : R → S of local rings with R Noetherian and an element of 𝔪_R ∖ 𝔪_R² killed by π; the maximal ideal of S then needs at least one generator fewer than that of R. Hence `Stacks.RegularLocalRing.SpanFinrank.ker_le_maximalIdeal_sq_of_surjective_of_spanFinrank_eq`: a surjection with unchanged embedding dimension has kernel in 𝔪_R².

Supporting public lemmas bound the minimal number of generators of the ideal of a list by its length (`Stacks.RegularLocalRing.QuasiRegular.spanFinrank_ofList_le`), show that the Krull dimension of a Noetherian local ring is a natural number (`Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim`), and find a unit coefficient in an expression of an element outside 𝔪² (`Stacks.RegularLocalRing.SpanFinrank.exists_isUnit_of_notMem_sq`).

The sequence proof inducts on the length of the list by killing a nonzerodivisor: the first generator is nonzero by minimality, R is a domain, and R/(x₁) is again regular local with the images of the other generators as a minimal generating list. The quotient and Cohen–Macaulay clauses are read off from the regular sequence. For the surjection, some coefficient of the killed element in a minimal generating set is a unit, so one generator becomes redundant in S.

Minimal list length is measured by `Submodule.spanFinrank`, and the dimension equalities are written additively. The module docstrings also announce the quasi-regularity of a minimal generating sequence (Tag 00NO), the generation of an ideal with regular quotient by part of a minimal generating set (Tag 00NR) and the comparison of kernels of surjections (Tag 00SE); none of these is in the file. They also name the domain theorem without its `stacks_` prefix.

Stacks Project, Tag 00NP and Tag 00NQ. The table of references below gives EGA 0 17.1.3, 17.1.4 and 22.5.2, EGA IV 16.9.12, 19.7.2 and 19.7.3, and SGA 4½ Cycle 2.2.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00NP](https://stacks.math.columbia.edu/tag/00NP) | `IsRegularLocalRing.stacks_isDomain` |  |
| [00NQ](https://stacks.math.columbia.edu/tag/00NQ) | `isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay` | Cohen-Macaulayness is the named predicate `Module.IsMaximalCohenMacaulay R R` \   (Definition 00NF), the equality `depth_𝔪(R) = dim R`; the minimal generating sequence is \   bound inside the clause that uses it, so the `in particular` is a statement about `R` alone. \   See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 17.1.4 | `isRegular_of_ofList_eq_maximalIdeal` | more general |
| EGA | IV 16.9.12 | `isRegular_of_ofList_eq_maximalIdeal` | necessity |
| EGA | IV 19.7.2 | `isRegular_of_ofList_eq_maximalIdeal` | (i), special case |
| EGA | IV 19.7.3 | `isRegular_of_ofList_eq_maximalIdeal` | partial |
| SGA | 4½ Cycle 2.2.1 | `isRegular_of_ofList_eq_maximalIdeal` | special case |
| EGA | 0 22.5.2 | `map_maximalIdeal_quotient_mk` | partial |
| SGA | 4½ Cycle 2.2.1 | `isRegular_of_ofList_eq_maximalIdeal` | special case |
| EGA | 0 17.1.3 | `isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay` | CM clause |
| SGA | 4½ Cycle 2.2.1 | `isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RegularLocalRing/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 72 declarations of the source file 19 are kept. The 53 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsRegularLocalRing.isDomain` is `IsRegularLocalRing.stacks_isDomain` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 11 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text. The 9 on kept declarations are listed above; the 2 on a declaration left out are not in the file.
