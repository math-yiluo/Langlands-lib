# Bounded complexes of finite free modules given by matrices

Module `StacksFrontier.Algebra.Homology.FiniteFreeComplex.BoundedFreeComplex`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a commutative ring `R`, the file sets up bounded complexes of finite free modules, in degrees `e`, …, `0`, with matrix differentials, and their own notions of exactness, isomorphism and triviality. It proves the first steps towards splitting off identity blocks over a Noetherian local ring of depth `0`.

## Main definitions

- `BoundedFreeComplex R`: a top degree `e : ℕ`, ranks `n : ℕ → ℕ` vanishing above `e`, and matrices `φ i : Matrix (Fin (n i)) (Fin (n (i+1))) R` for the differential from degree `i+1` to degree `i`, with `φ i * φ (i+1) = 0`.
- `BoundedFreeComplex.Exact`: `ker φ i = range φ (i+1)` for all `i ≤ e`, i.e. exactness in degrees `1`, …, `e`, including injectivity of the map out of degree `e`; nothing is required in degree `0`.
- `BoundedFreeComplex.Iso C D`: equal ranks and change-of-basis matrices `P i` with unit determinant such that `P i * φ_D i = φ_C i * P (i+1)`.
- `IsPartialPerm M`: entries `0` or `1`, at most one `1` in each row and column. `IsTrivial D`: every differential is a partial permutation matrix. `Trivializable C`: `C` is isomorphic to a trivial complex with the same length and ranks.
- `totalRank C`: the sum of the ranks.

## Main results

- `depth_zero_witness`: for `R` Noetherian local with maximal ideal `m` an associated prime of `R`, there is `x ≠ 0` with `m x = 0`.
- `unit_entry_of_exact`: under that hypothesis, if `C` is exact, `j ≤ e`, `n (j+2) = 0` and `n (j+1) > 0`, then `φ j` has a unit entry. (`injective_has_unit_entry`, despite its name, only gives an entry `a` with `a * x ≠ 0`.)
- `exists_block_form_of_unit_entry`: a matrix with a unit entry becomes `diag(1, ψ)` after multiplication by invertible matrices on both sides.
- `iso_exact` and `iso_trivializable`: exactness and trivializability transfer along isomorphisms of complexes of the same length.
- `exists_iso_blockDiag_one`: for exact `C` over such `R` and a top nonzero index `t ≥ 1` (`n t > 0`, `n (t+1) = 0`), `C` is isomorphic to an exact complex with the same ranks in which the differential out of degree `t` is `diag(1, ψ)` and, if `t ≥ 2`, the next differential has zero pivot column.

Helpers (`top_index`, `trivializable_of_top_zero`) prepare the induction carried out in another file.

## Watch for

- `Iso`, `Exact` and `IsTrivial` are the library's matrix-level notions, not Mathlib's categorical isomorphisms or exactness of complexes of modules.
- The full trivialization of exact complexes is not proved here.

## References

Tag 00MS, for `BoundedFreeComplex`. Places in SGA are in the table of references below.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00MS](https://stacks.math.columbia.edu/tag/00MS) | `BoundedFreeComplex` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 4½ Rapport 4.11 | `BoundedFreeComplex` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/FiniteFreeComplex/BoundedFreeComplex.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 42 declarations of the source file 41 are kept. The 1 left out are not needed by the results for which the extract is made: `BoundedFreeComplex.Iso.symm`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
