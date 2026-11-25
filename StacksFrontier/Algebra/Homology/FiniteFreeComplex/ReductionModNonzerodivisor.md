# Reducing an exact complex of finite free modules modulo a nonzerodivisor

Module `StacksFrontier.Algebra.Homology.FiniteFreeComplex.ReductionModNonzerodivisor`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a commutative ring `R`, consider a complex of finite free modules given by matrices `φ i` (`i : ℕ`) from the free module of rank `n (i+1)` to that of rank `n i`. The file proves that exactness survives reduction modulo a nonzerodivisor `x`, except at the lowest spot: if the complex is exact at positions `1, …, e`, then the reduced complex over `R/xR` is exact at positions `2, …, e`.

## Definitions

- `IsMatrixComplex n φ`: `φ i * φ (i+1) = 0` for all `i`.
- `ExactAtSucc n φ i`: `ker (φ i) = range (φ (i+1))`, i.e. exactness at the free module of rank `n (i+1)`, position `i+1`.
- `reduceMat x n φ`: the matrices reduced entrywise along `R → R/xR`.

## Main results

- `tag_00MZ`: let `R` be a local ring (`[IsLocalRing R]`), `φ` a matrix complex, and `x` a nonzerodivisor in the form `x * r = 0 → r = 0`. If `ExactAtSucc n φ i` holds for all `i < e`, then `ExactAtSucc n (reduceMat x n φ) i` holds for all `1 ≤ i < e`.

## Proof

A cycle of the reduced complex is lifted to a vector `v` over `R`; its image under the differential is `x · w` for some `w`, and cancelling `x` shows that `w` is a cycle, so `w` is the image of some `u` by exactness. Then `v - x · u` is a cycle, hence a boundary by exactness again, and reducing a preimage gives the result.

## Watch for

- The statement does not contain the hypothesis `x ∈ m` that the docstring and the source mention; it holds for any nonzerodivisor. The local-ring hypothesis is assumed but is not used in the proof.
- The complex is an `ℕ`-indexed family of matrices with no condition `n (e+1) = 0`; the source's bounded complex, with free terms in degrees `e`, …, `0`, is the case where the ranks vanish above `e`, and then exactness at position `e` is injectivity of the top map.
- The indexing is shifted: `ExactAtSucc n φ i` is exactness at position `i+1`.

## References

Tag 00MZ.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00MZ](https://stacks.math.columbia.edu/tag/00MZ) | `tag_00MZ` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/FiniteFreeComplex/ReductionModNonzerodivisor.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 6 are kept. The 1 left out are not needed by the results for which the extract is made: `reduceMat_isComplex`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
