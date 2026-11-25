# Analytic unramifiedness of Nagata local domains

Module `StacksFrontier.RingTheory.AnalyticallyUnramified.Criteria.NagataDomain`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A local domain that is Nagata has reduced completion at its maximal ideal.

`StacksIsAnalyticallyUnramified.of_isNagataRing` proves this for a commutative local domain R given `hR : StacksIsNagataRing R`. The proof is exposed as `Stacks.AnalyticallyUnramified.NagataDomain.solution`. The auxiliary lemmas `le_of_mem_associatedPrimes` and `mem_minimalPrimes_of_height_eq_one` show that an associated prime of A ⧸ I contains I and that a height-one prime of a domain containing a nonzero x is minimal over (x).

The argument inducts on a natural bound for the Krull dimension. In dimension zero the maximal ideal is zero and completion leaves the ring isomorphic to itself. For the induction step the normalization S of R is finite because a Nagata domain is Japanese. The completion of R embeds into the product of the completions of S localized at primes above the maximal ideal, by flatness and the completion formula for finite algebras. These localizations are normal Nagata domains of dimension bounded by that of R. In each one, the proof cuts by a nonzero element of the maximal ideal. The associated primes of the quotient have height one and are minimal over the principal ideal. Their localizations are regular, and their prime quotients are Nagata local domains of smaller dimension. The cutting criterion then gives reducedness of the completion.

Noetherianity is part of `StacksIsNagataRing`. The domain hypothesis also makes the zero ideal prime, which gives the Japanese property of R from the Nagata condition on its prime quotients. The module docstring names the theorem and the predicates without the prefix `Stacks`.

## References

Stacks Project Tag 0331, Tag 032X, Tag 032R, Tag 032T, Tag 032U, Tag 00OK, Tag 07N9, Tag 031T, Tag 00PD, and Tag 0330.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0331](https://stacks.math.columbia.edu/tag/0331) | `StacksIsAnalyticallyUnramified.of_isNagataRing` | Nagata is `IsNagataRing` of Definition 032R(2), whose first conjunct is \   `IsNoetherianRing R`, so the source's Noetherian hypothesis is absorbed rather than restated; \   analytically unramified is the predicate of Tag 032X, reducedness of the `𝔪`-adic completion. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AnalyticallyUnramified/Criteria/NagataDomain.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsAnalyticallyUnramified.of_isNagataRing` is `StacksIsAnalyticallyUnramified.of_isNagataRing` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
