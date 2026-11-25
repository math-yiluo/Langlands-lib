# Nagata rings under quasi-finite extension

Module `StacksFrontier.RingTheory.Nagata.QuasiFinite`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A Nagata ring is Noetherian and has Japanese, or N-2, quotients by all prime ideals. This file proves that the property ascends to an algebra of finite type with finite-dimensional fibres.

`isNagataRing_of_quasiFinite` says that a commutative R-algebra S is Nagata if R is Nagata and S satisfies both `Algebra.FiniteType R S` and `Algebra.QuasiFinite R S`. The source and target rings are in the same Lean universe.

Finite type gives Noetherianity of S. For each prime q of S, set p to its contraction to R. The helper for ideals lying over one another gives quasi-finiteness of R/p → S/q by passing to the quotient and restricting scalars. The induced map is injective, so the quasi-finite ascent theorem for Japanese domains transfers the property from R/p to S/q.

Mathlib's `Algebra.QuasiFinite` supplies fibre finiteness. The separate finite type instance is part of quasi-finiteness in the Stacks sense. The original algebra map can have a kernel, as for a quotient map.

Stacks Project Tag 032T, with Tag 032I for Japanese ascent, Tag 032R for the Nagata predicate, and Tag 00PL for quasi-finiteness.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032T](https://stacks.math.columbia.edu/tag/032T) | `isNagataRing_of_quasiFinite` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/QuasiFinite.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
