# Rank of rational function fields under an algebraic extension of coefficients

Module `StacksCore.FieldTheory.MvRatFunc.Algebra`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an algebra `S` over `R`, the file makes the library's `MvRatFunc σ S` an algebra over `MvRatFunc σ R` and computes its rank.

- `MvRatFunc.algebra R S σ`: this algebra structure, for `S` a domain with `FaithfulSMul R S`, induced on fraction rings by `R → S`. `algebraMap_algebraMap_mvPolynomial` (`simp`): the evident square from `MvPolynomial σ R` commutes.
- `MvRatFunc.rank` (`simp`): if moreover `S/R` is algebraic, the rank of `MvRatFunc σ S` over `MvRatFunc σ R` is that of `S` over `R`, lifted to a common universe. It is Mathlib's `Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial`.
- `MvRatFunc.finite_iff` (`simp`): for `S/R` algebraic and `S` free over `R`, `MvRatFunc σ S` is finite over `MvRatFunc σ R` iff `S` is finite over `R`.

## Watch for

`MvRatFunc.algebra` is an `abbrev`, not a global instance; the file activates it locally, and users must do the same.

## References

Tag 0G1M.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0G1M](https://stacks.math.columbia.edu/tag/0G1M) | `rank` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/FieldTheory/MvRatFunc/Algebra.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `MvRatFunc.rank'`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
