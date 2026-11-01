# Proof of the ordered derivative family Leibniz bound

This module proves the published proposition
`Langlands.Analysis.OrderedDerivativeFamilyLeibnizStatement` (module
`Langlands.Analysis.OrderedDerivativeFamilyLeibnizStatement`) as the theorem

```text
Langlands.Analysis.orderedDerivativeFamilyLeibniz
    (v : A → E) (B : F →L[ℝ] G →L[ℝ] H) :
    OrderedDerivativeFamilyLeibnizStatement (I := I) (J := J) v B
```

for every finite direction type `A`, all finite family index types `I` and `J`,
all real normed spaces `E`, `F`, `G`, `H`, every direction family `v` and every
continuous bilinear map `B`. Its seven universe parameters
`uA uI uJ uE uF uG uH` are independent. No hypothesis is added. The bound holds
for every order `p`, including `0`, every open set `S`, all families whose
members are `ContDiffOn ℝ ∞` on `S`, and every `x ∈ S`. The types `A`, `I` and
`J` may be empty.

Below, `T_p(f)` is `orderedDerivativeFamilyNorm v p f x`. This is the Euclidean
norm of the array of all values `iteratedFDeriv ℝ p (f i) x (v ∘ w)`, over
indices `i` and words `w : Fin p → A`.

The proof is internal elementary analysis by Worker 94. Its only classical
ingredient is the Leibniz rule for a bilinear product. The module imports only
the statement module; that module's import closure is
`Langlands.Analysis.OrderedDerivativeFamilyNorm` and Mathlib. The proof uses the
lemmas published with `orderedDerivativeFamilyNorm`.

## Auxiliary lemmas

These are Lean-`private` declarations of this module, so other modules cannot
import them.

- `finiteFamilyL2Norm_sq`: the square of `finiteFamilyL2Norm f` is
  `∑ i, ‖f i‖ ^ 2`.
- `finiteFamilyL2Norm_bilinear_le`: for vectors `f : I → F` and `g : J → G`,
  the family `(i, j) ↦ B (f i) (g j)` has `finiteFamilyL2Norm` at most
  `‖B‖ * finiteFamilyL2Norm f * finiteFamilyL2Norm g`. Each
  `‖B (f i) (g j)‖ ^ 2` is at most `(‖B‖ * ‖f i‖ * ‖g j‖) ^ 2`, by
  `ContinuousLinearMap.le_opNorm₂`. The double sum of these bounds factors
  exactly as `‖B‖ ^ 2 * (∑ ‖f i‖ ^ 2) * (∑ ‖g j‖ ^ 2)`. The two nonnegative
  sides are then compared through their squares (`sq_le_sq₀`).
- `orderedDerivativeFamilyNorm_congr_eventually`: if each member of one family
  agrees near `x` with the corresponding member of another, the two families
  have the same `T_p` at `x` (`Filter.EventuallyEq.iteratedFDeriv`).
- `contDiffOn_fixed_lineDeriv`: if `f` is `C^∞` on an open set `S`, then
  `y ↦ fderiv ℝ f y a` is `C^∞` on `S` (`ContDiffOn.fderiv_of_isOpen` and
  `ContDiffOn.clm_apply`).
- `orderedDerivativeFamilyNorm_prod_swap`: `T_p` of a family indexed by
  `A × (I × J)` equals `T_p` of the same family reindexed by `I × (A × J)`.
  The proof commutes finite sums.

## Induction on the order

The auxiliary theorem `orderedDerivativeFamilyLeibniz_aux` proves the bound for
`I : Type (max uA uI)` and `J : Type (max uA uJ)`. It uses induction on `p`,
generalizing over `I`, `J` and the two families. The induction step replaces an
index type by its product with `A`, and these two universe levels are unchanged
by that product.

*Order zero.* By `orderedDerivativeFamilyNorm_zero`, both sides become
finite-family norms of values at `x`. The right-hand sum has the single term
`l = 0`, with coefficient `1`. The bound is then
`finiteFamilyL2Norm_bilinear_le`.

*Step from `p` to `p + 1`.* Set `df (a, i) = (y ↦ fderiv ℝ (f i) y (v a))`, and
define `dg (a, j)` in the same way from `g`. These families are `C^∞` on `S`.
By `orderedDerivativeFamilyNorm_lineDeriv`, `T_l(df) = T_{l+1}(f)` and
`T_l(dg) = T_{l+1}(g)` for every `l`.

The same lemma, applied to the product family, rewrites the left-hand side
`T_{p+1}((i, j) ↦ B (f i) (g j))` as `T_p` of the family
`(a, (i, j)) ↦ (y ↦ fderiv ℝ (z ↦ B (f i z) (g j z)) y (v a))`. Every point of
the open set `S` has a neighborhood inside `S`. On `S` the bilinear product rule
`ContinuousLinearMap.fderiv_of_bilinear` writes this family as `R + L`, where

```text
R (a, (i, j)) = (y ↦ B (f i y) (dg (a, j) y)),
L (a, (i, j)) = (y ↦ B (df (a, i) y) (g j y)).
```

Hence both families have the same `T_p` at `x`, by
`orderedDerivativeFamilyNorm_congr_eventually`. The families `R` and `L` are
`C^∞` on `S` (`ContDiff.comp₂_contDiffOn` applied to
`B.isBoundedBilinearMap.contDiff`). The finite-family triangle inequality
`orderedDerivativeFamilyNorm_add_le` then gives
`T_p(R + L) ≤ T_p(R) + T_p(L)`.

For `R`, first reindex with `orderedDerivativeFamilyNorm_prod_swap`. Then apply
the induction hypothesis to `f`, indexed by `I`, and `dg`, indexed by `A × J`.
Since `T_{p-l}(dg) = T_{p+1-l}(g)` for `l ≤ p`, this gives

```text
T_p(R) ≤ ‖B‖ ∑_{l=0}^{p} choose(p, l) T_l(f) T_{p+1-l}(g).
```

For `L`, apply the induction hypothesis to `df`, indexed by `A × I`, and `g`.
Inside the sums, regroup `(A × I) × J` as `A × (I × J)`. This gives

```text
T_p(L) ≤ ‖B‖ ∑_{l=0}^{p} choose(p, l) T_{l+1}(f) T_{p-l}(g).
```

Pascal's identity, in the form of Mathlib's `Finset.sum_choose_succ_mul`,
combines the two sums into

```text
‖B‖ ∑_{l=0}^{p+1} choose(p + 1, l) T_l(f) T_{p+1-l}(g).
```

No factor depending on `A`, on the families or on the order enters.

## Universe transport

The final theorem `orderedDerivativeFamilyLeibniz` applies the auxiliary
theorem to `ULift.{uA} I` and `ULift.{uA} J`, with the families composed with
`Equiv.ulift`. The lemma `orderedDerivativeFamilyNorm_reindex`, for
`Equiv.ulift` and for their product `Equiv.prodCongr`, shows that this changes
neither the left-hand side nor any term on the right. The result is exactly
`OrderedDerivativeFamilyLeibnizStatement (I := I) (J := J) v B`, with the
original independent universes.

## Scope

All estimates compare finite real numbers. The theorem proves only this
algebraic Leibniz bound. It makes no claim about frozen actions, weighted
factorial bounds, elliptic regularity or automorphic growth.
