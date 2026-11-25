# Projective dimension along a well-ordered filtration (Auslander)

Module `StacksFrontier.Algebra.Homology.ProjectiveDimension.Filtration`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a ring and `M` an `R`-module exhausted by a monotone family of submodules `N e` indexed by a well-ordered type `E`. Auslander's theorem bounds the projective dimension of `M` by those of the graded pieces `N e / ⨆ e' < e, N e'`. The file proves it.

## Main results

- `ModuleCat.hasProjectiveDimensionLT_of_monotone_of_iSup_eq_top`: for `M : ModuleCat.{v} R` with `Small.{v} R`, `E` linearly and well ordered, `N : E → Submodule R M` monotone with `⨆ e, N e = ⊤`, if every graded piece satisfies `HasProjectiveDimensionLT _ n`, so does `M`. It restates `Stacks.ProjectiveDimension.FiltrationBound.solution`.
- Private lemmas: transfinite induction in a complete lattice (`iSup_le_of_le_biSup_lt_sup`); a module whose graded pieces are all projective is isomorphic to their direct sum, hence projective (`projective_of_iSup_eq_top`); and a bound `< m` for a graded piece of a kernel, from bounds `< m` for the source piece and `< m + 1` for the image piece, through their short exact sequence (`hasProjectiveDimensionLT_gradedKer`).

## How it is proved

By induction on `n`, in three cases. For `n = 0` the graded pieces vanish and transfinite induction makes `M` zero. For `n = 1` sections of the projections give an isomorphism from the direct sum of the graded pieces onto `M`: injective by looking at the largest index in a nonzero element, surjective by transfinite induction. For `n = m + 2`, `M` is a quotient of the free module `M →₀ Shrink R`, filtered by spans of basis vectors. The induced filtration of the kernel has graded pieces of projective dimension `< m + 1`, by short exact sequences with projective middle term, and the bound for `M` follows.

## Watch for

- The bound is stated as `HasProjectiveDimensionLT M n`; the source's `≤ n` is the case `n + 1`, and `n = 0` says that `M` is zero.
- `Small.{v} R` is assumed, so that `ModuleCat.{v} R` has enough projectives; only `Ring R` is needed, not commutativity.
- The source's family of submodules well ordered by inclusion is encoded as a monotone family over a well-ordered type, and its union as `⨆ e, N e = ⊤`.

## References

- Tags 0D1U, 065Q, 065R, 065S, 065T, 00O6.
- M. Auslander, *On the dimension of modules and algebras. III. Global dimension*, Nagoya Math. J. 9 (1955), 67–77.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0D1U](https://stacks.math.columbia.edu/tag/0D1U) | `ModuleCat.hasProjectiveDimensionLT_of_monotone_of_iSup_eq_top` | Indexed by `HasProjectiveDimensionLT _ n`, so that the source's `≤ n` is the case `n + 1`; the source's well-ordered family of submodules is a `Monotone` family over a type with `[LinearOrder E] [WellFoundedLT E]`, its union is `⨆ e, N e = ⊤`, and the graded piece at `e` is `↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)`. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Homology/ProjectiveDimension/Filtration.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
