# Finite-dimensional spaces of functions

Two general facts about a finite-dimensional complex subspace `V` of the functions `X → ℂ`.

- `exists_finset_eval_injective`: if `finrank V = r`, there is a finite set `T ⊆ X` with at most
  `r` points such that every `f ∈ V` vanishing on `T` is zero (unisolvent points). The proof is
  by strong induction on `r`: pick `f₀ ≠ 0` in `V` and `x₀` with `f₀ x₀ ≠ 0`; the subspace of
  `V` vanishing at `x₀` has smaller dimension.
- `mem_of_hasDerivAt`: if `t ↦ F t` is a family of elements of `V` (`t ∈ ℝ`) and for every `x`
  the function `t ↦ F t x` has derivative `F' x` at `0`, then `F' ∈ V`. The difference
  quotients lie in `V`, they converge pointwise (in the product topology) to `F'`, and a
  finite-dimensional subspace is closed.

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
