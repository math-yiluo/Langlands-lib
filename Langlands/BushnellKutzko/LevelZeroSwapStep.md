# Injectivity of compression by an adjacent block transposition

The theorem `compressionMap_swap_comp_eq_zero` supplies the transposition
step in the proof of diagonal compression injectivity. Let `i, j = i + 1`
be adjacent blocks of the standard principal order, `s = pairGL swapU` their
transposition, and `K = U^1(𝔄)`. Let `g : W → V` be a linear map into the
`K`-fixed vectors of a smooth representation `π` with operators `τ A D` on
`W` such that `g ∘ τ A D = π(diag(A, D)) ∘ g` for integral `A, D` with
integral inverses. Assume `∑_Z τ (unipLift r Z) 1 = 0` for `0 < r < f`, with
`Z` ranging over `M_f(𝓀[F])`. The operator `unipLift r Z` lifts the
unipotent whose off-diagonal entries are the upper right `r × (f - r)`
corner of `Z`. If compression by `s` kills `g`, then `g = 0`.
[Principal lemma](LevelZeroPrincipal.md)

## Proof

The kernel of `thetaHom`, the residue of the `(j, i)` block, fixes `π(s) v`
whenever `v` is `K`-fixed. The lifted lower unipotents
`t_Y = pairGL (lowerU (liftM Y))` form a section. By
`averageMap_eq_mean_of_hom`, compression by `s` is
`|M_f(k)|⁻¹ ∑_Y π(t_Y) π(s)` on `K`-fixed vectors. Using the formula for the
inner compression and conjugating the `t_Y` by `s` gives
`A_s (A_s v) = |M_f(k)|⁻¹ ∑_X e_K π(pairGL (upperU (liftM X))) v`.

For `v = g w`, the proof evaluates the terms in this sum in three cases.

- For `X = 0`, the lift has zero residue, so the upper unipotent belongs to
  `K`. Its averaged action on `g w` is `g w`.
- For invertible `X`, `upperU_eq_of_isUnit` writes the lifted unipotent as
  `l s d l`, with `l ∈ K` and `d` block diagonal. The term is
  `A_s (g (τ d w))`, which vanishes by hypothesis.
- For nonzero singular `X`, `exists_erMat_form` reduces to the rank matrix
  `E = erMat F r` after block diagonal conjugation and correction by an
  element of `K`. The block diagonal conjugator normalizes `K`. The identity
  `lowerU_mul_upperU` makes the rank-matrix term invariant under precomposing
  its argument with `τ (unipLift r Z) 1` for every `Z`. Summing and applying
  the assumed vanishing shows that the term is zero.

Thus `A_s (A_s (g w)) = |M_f(k)|⁻¹ g w`. Since the scalar is nonzero over
`ℂ`, the assumed equation `A_s ∘ g = 0` implies `g = 0`.
