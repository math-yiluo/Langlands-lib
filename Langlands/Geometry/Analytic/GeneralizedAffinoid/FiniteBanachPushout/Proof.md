# Finite Banach base change in the actual affinoid pushout

Worker 271 proves
`Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout.FiniteBanachPushoutStatement`.
For every complete ultrametric normed field `K`, every three presented affinoid
algebras `A`, `B`, `C`, and every bounded pair `f : A → B`, `g : A → C`,
finite Banachness of `f` implies finite Banachness of the original map
`AffinoidPushout.rightMap f g : C → AffinoidPushout.algebra f g`.
The theorem `finiteBanachPushout` has exactly that statement as its type.

The proof uses the existing closed-quotient pushout and its original bounded
maps. It neither changes the definition of `IsFiniteBanach` nor assumes a
nontrivial valuation, strict radii, nonzero algebras, or nonempty spectra.
This prerequisite alone does not prove analytic étale pointwise lifting.

## Exact lifts from approximate lifts

`exists_normControlledLifts_of_approx` concerns a continuous linear map `L`
from a complete normed vector space `E` to a normed vector space `F`, over any
normed field. Its supplied hypothesis gives, for each `y`, an `x` with
`dist (L x) y ≤ ‖y‖ / 2` and `‖x‖ ≤ C * ‖y‖`, where `C ≥ 0`.

Choose one such approximate lift `g y` and put `h y = y - L (g y)`.
Induction bounds `‖h^[n] y‖` by `2⁻ⁿ * ‖y‖`. The corrections
`g (h^[n] y)` have summable norms bounded by the corresponding geometric
series with initial value `C * ‖y‖`. Completeness of `E` gives their sum `x`.
The partial sums telescope under `L` to `y - h^[n] y`. Continuity of `L`
and uniqueness of limits prove `L x = y`. The norm of the sum is at most
`(2 * C + 1) * ‖y‖`, with this deliberately relaxed constant strictly positive.

This argument adapts only the second step of Mathlib's
`ContinuousLinearMap.exists_preimage_norm_le`. The Baire and scalar-rescaling
first step is replaced by the explicit approximate-lift hypothesis. Thus no
nontrivial-valuation hypothesis is used. Completeness of `F` is unnecessary.

## Algebraic tensor coefficient estimate

`exists_coefficient_lift_representation` starts with generators `b : Fin n → B`
whose coefficient map for `f` has lifts bounded by `M > 0`, and an original
bound `N > 0` for `g`. Let `t` have a finite tensor representation `r`.
Its value is the maximum of `‖r.left i‖ * ‖r.right i‖`, including the empty case.

Lift each `r.left i` to coefficients `a i : Fin n → A` with
`‖a i‖ ≤ M * ‖r.left i‖`, and define
`c j = ∑ i, g (a i j) * r.right i` in `C`.
Expanding the two finite sums and applying the full bounded-map equality
`leftMap.comp f = rightMap.comp g` proves that the coefficient map for
`rightMap`, with generators `leftMap (b j)`, sends `c` to the algebraic
tensor image of `t`. This is equality in the actual pushout algebra.

The maximum product norm on `A^n` bounds each `a i j` by `‖a i‖`.
Ultrametricity bounds each finite sum defining `c j` by the largest term.
The result is `‖c‖ ≤ (N * M) * r.value`, independent of the number of tensor
terms. This estimate does not need completeness of `K`.

## Completion and the actual pushout

`rightMap_isFiniteBanach` uses the published admissibility of the actual
`tensorMap` from the genuine projective completed tensor algebra onto the
pushout. Fix a positive lift constant `H` for this map and a positive bound
`P` for the map itself. A pushout element `z` lifts to `y` with
`‖y‖ ≤ H * ‖z‖`.

For `z ≠ 0`, approximate `y` by an algebraic tensor `t` at distance less than
`ε = ‖z‖ / (2 * (P + 1))`. Since `ε ≤ ‖z‖`, the isometric map from the
seminormed algebraic tensor to its Hausdorff completion gives
`‖t‖ < (H + 1) * ‖z‖`. The algebraic tensor norm is the infimum of the values
of its finite-max representations. Hence some representation `r` has value
less than `(H + 1) * ‖z‖`; no nondegeneracy of the algebraic seminorm is assumed.

The preceding coefficient estimate gives an approximate coefficient lift
with norm at most `N * M * (H + 1) * ‖z‖`. Its image differs from `z` by at
most `P * ε ≤ ‖z‖ / 2`. For `z = 0`, the zero coefficient vector suffices.
Apply the first lemma to this coefficient map from the complete finite
product `C^n`. It yields exact lifts with the positive uniform bound
`2 * (N * M * (H + 1)) + 1`. These are precisely the generators and controlled
lifts required by `IsFiniteBanach`.

Finally, `finiteBanachPushout` applies `rightMap_isFiniteBanach` to each pair
of original maps, proving the unchanged target proposition.

## Provenance

This is an internal derived proof of the published statement, using the
existing finite Banach coefficient maps, ultrametric projective tensor
seminorm, completed tensor algebra, and admissible tensor quotient. Worker 271
authored the complete shared proof and its mathematical explanation; Worker 640
inspected the draft and prepared this proof pair for independent review.
The approximate-lift argument adapts the second step of Mathlib's
`ContinuousLinearMap.exists_preimage_norm_le` in
`Mathlib/Analysis/Normed/Operator/Banach.lean`, with an explicit nonnegative
constant and approximate-lift hypothesis replacing the open mapping input.
No new external theorem is claimed as the source of the full pushout result.
