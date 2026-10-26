# Existence of the numerical block cone

Author: Worker 23.

The theorem `Langlands.glBlockConeExists` proves exactly
`Langlands.GLBlockConeExistenceStatement` from
`Langlands.Representation.Classification.ParabolicConeAuxiliaryStatement`.
For every rank `n` (including `n = 0` and the empty block shape), every block
shape `B` of `n` and every real vector `r` indexed by the blocks of `B`, it
produces a block shape `C`, a labelling `q : Fin B.length → Fin C.length` and
real values `t` satisfying `GLBlockConeNumericalConditions B C r q t`. These
conditions say that `q` is monotone and surjective, that the size of each coarse
block is the sum of the fine sizes in its fibre, that `t` is strictly
decreasing, that the sum of `r` over each fibre is the coarse size times `t`, and
that every inclusive prefix of the residuals `r k - B.size k * t (q k)` inside a
fibre is nonpositive.

The proof is elementary and internal. It uses Mathlib's `Fin.predAbove` lemmas and
finite-sum algebra. It does not use any published cone uniqueness or matrix
result. The route is the pool adjacent violators algorithm: adjacent fibres are
merged until the fibre means strictly decrease.

## Index lemmas

`val_predAbove` computes `Fin.predAbove p a` as `a - 1` above `p` and `a`
otherwise. Two consequences follow. `predAbove_eq_self_iff` says exactly the two
labels `p.castSucc` and `p.succ` map to `p`. `predAbove_eq_predAbove_iff` says
the map is injective away from `p`.

## Poolings

Fix block weights `w : Fin L → ℕ`, all positive, and values `r : Fin L → ℝ`. For
a labelling `q : Fin L → Fin m` the module defines:

- `fibre q j`, the set of indices with label `j`;
- `fibreWeight w q j`, the real sum of the weights over that fibre;
- `fibreMean w r q j`, the sum of `r` over the fibre divided by its weight.

The structure `IsPooling w r q` asks three things. The labelling `q` is monotone
and surjective. For every index `i`, the sum of `r k - w k * fibreMean w r q (q i)`
over the indices `k ≤ i` with `q k = q i` is nonpositive. Surjectivity makes
every fibre weight positive (`fibreWeight_pos`). Hence the sum of `r` over a
fibre equals its weight times its mean (`sum_fibre_eq`).

`isPooling_id` says the identity labelling is a pooling. Each fibre is the
singleton `{i}`, so its mean is `r i / (w i : ℝ)`, normalized by the weight. The
only residual term is `r i - (w i : ℝ) * (r i / (w i : ℝ))`, which is zero
because `w i` is positive. Hence every residual prefix is zero.

## Merging two adjacent fibres

`IsPooling.merge` takes a pooling `q : Fin L → Fin (m + 2)` and a position
`p : Fin (m + 1)`. Assume the mean of the fibre at `p.castSucc` is at most the
mean of the fibre at `p.succ`. Then `fun k => p.predAbove (q k)` is again a
pooling. Monotonicity and surjectivity pass through `Fin.predAbove`. The merged
fibre over `p` is the disjoint union of the two old fibres. Its weighted mean
`μ` satisfies `(W₁ + W₂) μ = W₁ μ₁ + W₂ μ₂`. Since `μ₁ ≤ μ₂`, this gives
`μ₁ ≤ μ ≤ μ₂`. The residual condition at an index `i` then has three cases.

- If `q i = p.castSucc`, monotonicity shows that the indices `k ≤ i` in the
  merged fibre all lie in the left fibre. The old residual prefix used the mean
  `μ₁ ≤ μ`, so each term only decreases.
- If `q i = p.succ`, the prefix is the whole left fibre together with the right
  fibre's prefix up to `i`. The left fibre contributes `W₁ (μ₁ - μ) ≤ 0`. The
  right part equals its old residual prefix, which is nonpositive, plus
  `w' (μ₂ - μ)`. Here `w'` is the weight of that part, with `w' ≤ W₂`. The two
  correction terms sum to at most `W₂ (μ₂ - μ) + W₁ (μ₁ - μ)`, and this sum is
  `0`. So the prefix stays nonpositive (`linarith`).
- Otherwise the new label of `i` is not `p`. By injectivity away from `p`, the
  fibre of `i`, its mean, and its residual prefixes are unchanged.

## Termination and the coarse shape

`exists_strictAnti_pooling` uses induction on the number `m` of labels. It
proves that every pooling can be coarsened to a pooling whose fibre means are
strictly decreasing. With zero or one label the means are strictly decreasing
vacuously. Otherwise, if the means are not strictly decreasing, then
`Fin.strictAnti_iff_succ_lt` gives an adjacent pair whose means are not strictly
decreasing. Merging that pair lowers the number of labels by one.

`glBlockConeExists` applies this to the identity pooling of the blocks of `B`,
weighted by `B.size`. The resulting labelling `q` has strictly decreasing means
`t = fibreMean B.size r q`. The coarse shape `C` has as block sizes the sums of
`B.size` over the fibres of `q`. These sizes are positive by surjectivity, and
they sum to `n` by `Finset.sum_fiberwise`. The six numerical conditions are then
the pooling fields, the definition of `C`, strict decrease of `t`, and
`sum_fibre_eq` after casting the natural fibre sums to `ℝ`. The construction
makes no case distinction on `n` or on the number of blocks, so the zero-rank
case is covered by the same argument.
