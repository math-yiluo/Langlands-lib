# Uniqueness of the numerical block cone

Author: Worker 379.

The theorem `Langlands.glBlockConeUnique` proves exactly
`Langlands.GLBlockConeUniquenessStatement` from
`Langlands.Representation.Classification.ParabolicConeAuxiliaryStatement`.
Fix a rank `n` (including `n = 0`), a block shape `B` of `n` and a real vector
`r` indexed by the blocks of `B`. Suppose `C, q, t` and `D, q', t'` both satisfy
`GLBlockConeNumericalConditions` for `B` and `r`. Then `C = D` as actual
`BlockShape n` structures. The proof uses no subgroup containment, no
positive-rank assumption, no existence result and no abstract cone theorem.

The argument is elementary and internal. It uses only finite-sum algebra and
order facts from Mathlib. It follows the summation-by-parts route suggested in
the task context. The helper lemmas live in the namespace
`Langlands.ParabolicConeUniqueness`.

## Shape extensionality

The proof reuses `Langlands.GeneralLinear.BlockShape.ext_of_size` from
`Langlands.Group.GL.AdjacentMergeShape`: two block shapes of the same rank are
equal when their lengths are equal and their sizes agree after `Fin.cast` along
that equality. The accepted contribution's duplicate `blockShape_ext` helper
was removed during integration; this existing theorem has the same statement.

## Summation by parts

`sum_mul_nonpos_of_antitone` concerns real vectors `e` and `v` on `Fin L`. It
assumes that `v` is antitone, that every inclusive prefix sum
`∑ k ≤ i, e k` is nonpositive, and that `∑ k, e k = 0`. It concludes
`∑ k, e k * v k ≤ 0`.

The proof is an induction on `m ≤ L`. For each real `c` that is at most `v k`
for all `k < m`, it shows that
`∑ k < m, e k * v k ≤ c * ∑ k < m, e k`. For `m = 0` both sides are zero. For
the step from `m` to `m + 1`, let `p` be the block with index `m`. The induction
hypothesis with the lower bound `v p` (valid because `v` is antitone) gives
`∑ k < m, e k * v k ≤ v p * ∑ k < m, e k`. Adding `e p * v p` bounds the new
partial sum by `v p` times the prefix sum up to `p`. That prefix sum is
nonpositive and `c ≤ v p`, so the bound by `c` times the prefix sum follows
(`nlinarith`). Finally a lower bound `c` of `v` exists because its range is
finite. With `m = L` the right side is `c * 0 = 0`.

## Residuals of one set of witnesses

For one set of witnesses `C, q, t` the module defines
`residual B r q t i = r i - B.size i * t (q i)`, with the natural size cast to
`ℝ`. Assume `GLBlockConeNumericalConditions B C r q t`.

- `residual_fibre_sum`: over each fibre `q i = j`, the residuals sum to zero.
  The sum of `r` over the fibre is `C.size j * t j` by the fibre-average
  equation. The sum of `B.size i * t (q i)` is also `C.size j * t j`, by the
  fibre-size equation cast to `ℝ`.
- `residual_sum_filter`: for every decidable predicate `P` on the coarse labels,
  the residuals over `{i | P (q i)}` sum to zero. This uses
  `Finset.sum_fiberwise`. Fibres with `P j` contribute their zero sum, and the
  others are empty.
- `residual_sum`: the residuals have total zero.
- `residual_mul_sum`: `∑ i, residual B r q t i * t (q i) = 0`, since `t (q i)`
  is the constant `t j` on each fibre.
- `residual_prefix`: every inclusive global prefix sum `∑ k ≤ i` of the
  residuals is nonpositive. Monotonicity of `q` splits the indices `k ≤ i` into
  the disjoint sets `{k | q k < q i}` and `{k | q k = q i ∧ k ≤ i}`. Here
  `Monotone.reflect_lt` shows that `q k < q i` implies `k < i`. The first set is
  a union of whole fibres, so its sum is zero by `residual_sum_filter`. On the
  second set `t (q k) = t (q i)`, so its sum is exactly the residual-prefix
  clause of the numerical conditions, which is nonpositive.
- `residual_mul_sum_nonpos`: for every antitone `v`,
  `∑ i, residual B r q t i * v i ≤ 0`, by the summation-by-parts lemma.
- `antitone_exponent`: `i ↦ t (q i)` is antitone. It is a strictly antitone
  function composed with a monotone one.

## Equal exponents

`exponent_eq` compares two sets of witnesses and proves `t (q i) = t' (q' i)`
for every fine block `i`. Write `a i = t (q i)`, `b i = t' (q' i)`, and `e`,
`e'` for the two residual vectors. Termwise algebra (`ring`) gives

`∑ k, B.size k * (a k - b k) ^ 2 = (∑ e k * b k - ∑ e k * a k) + (∑ e' k * a k - ∑ e' k * b k)`.

The identity holds because `e k - e' k = B.size k * (b k - a k)`. Both `b` and
`a` are antitone, so the first and third sums on the right are nonpositive by
`residual_mul_sum_nonpos`. The second and fourth sums vanish by
`residual_mul_sum`. Hence the weighted sum of squares is nonpositive. Its terms
are nonnegative, so each term is zero (`Finset.sum_eq_zero_iff_of_nonneg`).
Since `B.size i` is positive, `(a i - b i) ^ 2 = 0`, so `a i = b i`.

`label_le_iff` then shows that `q i ≤ q k` holds exactly when `q' i ≤ q' k`.
Both are equivalent to `a k ≤ a i` by `StrictAnti.le_iff_ge` for `t` and for
`t'`, using `exponent_eq`.

## Equal labellings and the coarse shape

`labels_eq` takes surjective maps `q : Fin L → Fin m` and `q' : Fin L → Fin m'`
that induce the same order on `Fin L`. It concludes that `m = m'` and that
`q' i = Fin.cast _ (q i)` for every `i`. Put `φ j = q' (Function.surjInv hq j)`.
Then `φ (q i) = q' i`: the chosen preimage of `q i` has the same `q`-label as
`i`, so it has the same `q'`-label by both directions of the order
equivalence. The same equivalence makes `φ` strictly monotone. Surjectivity of
`q'` makes `φ` surjective. So `φ` is a bijection and
`Fintype.card_of_bijective` gives `m = m'`. After substituting this equality,
`φ` is a strictly monotone surjection of `Fin m` onto itself. Since `φ` and
`id` are strictly monotone with the same range,
`StrictMono.range_inj_of_wellFoundedLT` gives `φ = id`.

`glBlockConeUnique` applies `labels_eq` with `label_le_iff`, using surjectivity
from both sets of conditions. This gives `C.length = D.length` and
`q' i = Fin.cast _ (q i)`. By the two fibre-size equations,
`C.size j` and `D.size (Fin.cast _ j)` are sums of `B.size` over the fibres
`q i = j` and `q' i = Fin.cast _ j`. These fibres are equal by `Fin.cast_inj`.
So `BlockShape.ext_of_size` gives `C = D`. No case is made on `n` or on `B.length`:
when `B` has no blocks, surjectivity forces both coarse lengths to be zero, and
the same argument applies.

The closing theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
