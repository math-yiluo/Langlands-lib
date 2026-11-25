# Descent of p-th roots from a local completion

Module `StacksFrontier.RingTheory.Nagata.PthRoot`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The maximal-ideal completion of a Nagata local domain of positive characteristic p detects which elements of the domain are p-th powers.

`StacksIsNagataRing.exists_pow_eq_iff_exists_pow_eq_adicCompletion` says that a ∈ A has a p-th root in A if and only if its image has a p-th root in the maximal-ideal adic completion. The characteristic is specified by `CharP A p` and `hp : p ≠ 0`, which imply primality of p for a domain. The hypothesis `hA : StacksIsNagataRing A`, the Nagata property of `StacksFrontier.RingTheory.Nagata.Defs`, supplies Noetherianity.

`Stacks.Nagata.PthRootDescent.mapAdicCompletion` constructs a ring map on completions for any commutative A-algebra B when I maps into J, using the compatible maps between quotients by powers. `AdjoinRoot.not_isReduced_adicCompletion_of_pow_eq` shows that if A is a Noetherian local domain of prime characteristic p and a has a p-th root in its completion, the maximal-ideal completion of B = A[X]/(Xᵖ − a) is nonreduced. It takes locality of B as an instance, supplied in the main proof by `Stacks.Nagata.PthRootDescent.isLocalRing_adjoinRoot`.

The forward implication is functoriality of powers. For descent, reducedness of the completion of A and Krull's intersection theorem exclude roots in the fraction field if A has none. Irreducibility over the fraction field then makes B a domain. It is local and Nagata by the root-adjunction lemma and finite type ascent, so its completion is reduced. The difference of the two roots gives a nilpotent there, while reduction modulo a suitable power of the maximal ideal and extraction of the linear coefficient show that the difference is nonzero.

The module docstring calls the main result by a name without the `Stacks` prefix of its declaration.

Stacks Project Tag 09E2, Tag 0331 (analytic unramifiedness), and Tag 0334 (finite type ascent).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09E2](https://stacks.math.columbia.edu/tag/09E2) | `StacksIsNagataRing.exists_pow_eq_iff_exists_pow_eq_adicCompletion` | Stated as a biconditional, the reverse implication being `map_pow` on the \   completion map. Noetherian is absorbed into `IsNagataRing` (Definition 032R(2)), primality of \   `p` into `p ≠ 0` over a domain (`CharP.char_is_prime_or_zero`), and the characteristic of \   `Frac A` is read off `A`. The completion is `AdicCompletion (maximalIdeal A) A` as in Tag 032X. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/PthRoot.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsNagataRing.exists_pow_eq_iff_exists_pow_eq_adicCompletion` is `StacksIsNagataRing.exists_pow_eq_iff_exists_pow_eq_adicCompletion` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
