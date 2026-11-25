# Exact complexes of finite free modules over a local ring of depth zero are trivial

Module `StacksFrontier.Algebra.Homology.FiniteFreeComplex.TrivialIsoOfExact`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a Noetherian local ring whose maximal ideal is an associated prime of `R`, i.e. of depth `0`. The file proves Stacks 00MY: a complex of finite free modules in degrees `e`, …, `0`, given by matrices and exact in degrees `e`, …, `1`, is isomorphic to a direct sum of trivial complexes. It works with the matrix complexes `BoundedFreeComplex` of an imported file.

## Main results

- `exists_trivial_iso_of_exact`: under these hypotheses, every exact `BoundedFreeComplex` `C` is isomorphic, in the sense of `BoundedFreeComplex.Iso` (degreewise change of basis with unit determinant), to a complex `D` with the same length and ranks whose differentials are all partial permutation matrices (`D.IsTrivial`).
- `BoundedFreeComplex.trivializable_of_exact`: the same statement phrased with `Trivializable`.
- `split_off_identity_block`: an exact complex with a nonzero term in positive degree yields an exact complex of strictly smaller total rank whose trivializability implies that of the original. `split_reduction` is the same for a given top nonzero degree `t ≥ 1`.
- `exists_exact_totalRank_lt_of_blockDiag_one`: the core step. If the differential out of the top nonzero degree `t ≥ 1` has the block form `diag(1, ψ)` and, for `t ≥ 2`, the next differential has zero pivot column, then removing the pivot row and column gives an exact complex `C'` of smaller total rank, and a trivialization of `C'` lifts to one of the original complex.

Helpers: `padBlock A`, the matrix `diag(1, A)`, with lemmas on its entries, products, inverse, determinant and the partial permutation property; `exact_eqn_reindex` (exactness is unchanged by reindexing along rank equalities); and `isPartialPerm_prepend_zero_col`.

## Proof

By strong induction on the total rank. If all terms in positive degree vanish, the complex is already trivial. Otherwise one takes the top nonzero degree `t`; by results of the imported file the differential out of degree `t` has a unit entry, and after a change of basis it has block form `diag(1, ψ)` with zero pivot column in the next differential. Dropping the identity block keeps the complex exact, (`ψ` is again injective, dropping the zero pivot column does not change the range of the next differential, and at the pivot cycles are lifted through the original complex), and lowers the total rank. A trivialization of the smaller complex is padded back by `padBlock` to one of the original.

## Watch for

- "Isomorphic" means the library's matrix-level `BoundedFreeComplex.Iso`, and "direct sum of trivial complexes" is expressed as "every differential is a partial permutation matrix" (`IsTrivial`), not as a categorical direct sum.
- Depth `0` is stated as `maximalIdeal R ∈ associatedPrimes R R`.
- Exactness is not required in degree `0`.

## References

Tag 00MY.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00MY](https://stacks.math.columbia.edu/tag/00MY) | `exists_trivial_iso_of_exact` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/FiniteFreeComplex/TrivialIsoOfExact.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
