# Expanding powers of an archimedean derivative over words

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerWords`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. These are helper lemmas for half (S) of the
Whittaker expansion (see `Interface`). The direction `Z` of the character derivative depends on the
point, so the functions `(R_Z)^K f` form an infinite family. This module bounds their Whittaker
functions by finitely many functions that do not depend on `Z`. The argument is elementary linear
algebra and is this project's own.

## Section `Words`

* `wordOp R D K l`, for a family `D : S → ArchimedeanMatrix` and a word `l : Fin K → S`, is the
  composite `R(D_{l 0}) ∘ ⋯ ∘ R(D_{l (K-1)})`. It is defined by recursion on `K`, with
  `wordOp R D 0 l = 1`.
* `pow_eq_sum_wordOp`: if `Z = Σ_s c(Z)_s D_s` for every `Z`, then
  `(R_Z)^K = Σ_l (Π_k c(Z)_{l k}) wordOp R D K l`. Proof: induction on `K`. `R` is real-linear.
  The words of length `K + 1` are reindexed as pairs (first letter, tail) by `Fin.consEquiv`.

## Section `Entries`

* `mixedBasis F` is the real basis `Module.finBasis ℝ` of the mixed space `F ⊗ ℝ`.
* `EntryIndex F n = Fin n × Fin n × Fin (dim_ℝ (F ⊗ ℝ))`.
* `entryUnit F n (a, b, k)` is the matrix with `e_k` at position `(a, b)` and zeros elsewhere
  (`Matrix.single`).
* `entryCoord F n Z (a, b, k)` is the `k`-th coordinate of the entry `Z_{ab}`.
* `eq_sum_entryCoord`: `Z = Σ_s entryCoord Z s • entryUnit s`. Proof:
  `Matrix.matrix_eq_sum_single`, the basis expansion of each entry, and linearity of
  `Matrix.single`.
* `coordConst F` is the sum of the operator norms of the coordinate functionals. These functionals
  are continuous because `F ⊗ ℝ` is finite-dimensional.
* `abs_entryCoord_le`: if every entry of `Z` has norm at most `A`, then every coordinate satisfies
  `|entryCoord Z s| ≤ coordConst F · A`.

## Section `Bound`

Let `(V, R)` be a `WhittakerDecayClass` and `ψ` a standard additive character.

* `WhittakerDecayClass.exists_bound_unipotent`: every `f ∈ V` is bounded on `N(𝔸) g`. Use the
  band bound with `lo = hi = |det g|_𝔸`. Unipotent elements have determinant `1`.
* `whittakerLinear F hV ψ hψ g`: the complex-linear functional `f ↦ W_f(g)` on `V`. Additivity
  is `whittaker_add`, which applies by the previous bound. Homogeneity is `whittaker_smul`.
* `entryWord K l = wordOp R entryUnit K l`.
* `norm_whittaker_pow_le`: if every entry of `Z` has norm at most `A`, then
  `‖W_{(R_Z)^K f}(g)‖ ≤ (coordConst F · A)^K Σ_l ‖W_{entryWord K l f}(g)‖`, where the sum runs
  over the finitely many words `l : Fin K → EntryIndex F (r + 1)`. Proof: expand `(R_Z)^K` by
  `pow_eq_sum_wordOp` and `eq_sum_entryCoord`. Apply the linear functional `whittakerLinear`, then
  the triangle inequality, and bound each coefficient product by `(coordConst F · A)^K`
  (`Finset.prod_le_prod₀`).
