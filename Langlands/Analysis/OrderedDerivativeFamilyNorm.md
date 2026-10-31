# Finite-family norms of ordered derivative tensors

The module `Langlands.Analysis.OrderedDerivativeFamilyNorm` imports only Mathlib.
It defines two noncomputable real numbers and proves helper identities and
estimates about them. It uses Mathlib's actual iterated real Fréchet derivatives
`iteratedFDeriv ℝ`.

## Definitions

Let `I` be a finite type and `F` a real normed space. For `f : I → F`,
`finiteFamilyL2Norm f` is `‖WithLp.toLp 2 f‖`, the norm of `f` in
`PiLp 2 (fun _ : I => F)`. Only `NormedAddCommGroup F` is needed for this
definition.

Let `E` and `F` be real normed spaces, `A` a finite type of direction indices,
`v : A → E` a family of directions, `p : ℕ` an order, `I` a finite family index,
`f : I → E → F` a family of functions and `x : E` a point. Then
`orderedDerivativeFamilyNorm v p f x` is `finiteFamilyL2Norm` of the complete
family indexed by `I × (Fin p → A)`, whose component at `(i, w)` is

`iteratedFDeriv ℝ p (f i) x (v ∘ w)`,

the `p`-th derivative of `f i` at `x` evaluated on the ordered word of
directions `v (w 0), …, v (w (p-1))`. Every ordered word occurs once, so repeated
directions keep their ordered multiplicities. No normalization, factorial or
dimension factor is inserted. The definition places no differentiability
condition on `f`; Mathlib's `iteratedFDeriv` is used as it is.

The types `A`, `I`, `J`, `E` and `F` have independent arbitrary universes. The
directions are arbitrary vectors; they need not be a basis or have norm one.
Empty families, empty direction sets and order zero are all allowed. If `I` is
empty, or `A` is empty and `p > 0`, the double sum in
`orderedDerivativeFamilyNorm_eq_sqrt` below is empty, so the norm is `0`.

## Results

- `finiteFamilyL2Norm_eq_sqrt`: `finiteFamilyL2Norm f = √(∑ i, ‖f i‖ ^ 2)`.
- `finiteFamilyL2Norm_nonneg`, `finiteFamilyL2Norm_add_le` (triangle inequality
  for `fun i => f i + g i`), `finiteFamilyL2Norm_congr` (pointwise equal
  families), and `finiteFamilyL2Norm_reindex`: for `e : I ≃ J`,
  `finiteFamilyL2Norm (f ∘ e) = finiteFamilyL2Norm f`.
- `orderedDerivativeFamilyNorm_eq_sqrt`: the norm equals
  `√(∑ i, ∑ w : Fin p → A, ‖iteratedFDeriv ℝ p (f i) x (v ∘ w)‖ ^ 2)`.
- `orderedDerivativeFamilyNorm_nonneg`: the norm is nonnegative.
- `orderedDerivativeFamilyNorm_zero`: at order `0` the norm is
  `finiteFamilyL2Norm (fun i => f i x)`, since the empty word is unique and the
  zeroth iterated derivative is the value.
- `orderedDerivativeFamilyNorm_reindex`: for `e : I ≃ J` and `f : J → E → F`,
  the family `fun i => f (e i)` has the same norm as `f`.
- `orderedDerivativeFamilyNorm_unique`: for `[Unique I]` the norm is
  `√(∑ w : Fin p → A, ‖iteratedFDeriv ℝ p (f default) x (v ∘ w)‖ ^ 2)`.
- `orderedDerivativeFamilyNorm_euclidean_singleton`: the exact elliptic case
  described below.
- `orderedDerivativeFamilyNorm_add_le`: if `ContDiffAt ℝ p (f i) x` and
  `ContDiffAt ℝ p (g i) x` for every `i`, the family
  `fun i y => f i y + g i y` has norm at most the sum of the norms of `f` and `g`
  at `x`. The hypotheses let Mathlib's `fun_iteratedFDeriv_add_apply` split each
  component; the triangle inequality is then that of `PiLp 2`.
- `iteratedFDeriv_fixed_lineDeriv`: if `ContDiffAt ℝ (p + 1) f x`, then for
  `m : Fin p → E` and a fixed `a : E`,
  `iteratedFDeriv ℝ p (fun y => fderiv ℝ f y a) x m =
  iteratedFDeriv ℝ (p + 1) f x (Fin.snoc m a)`.
  The proof composes `fderiv ℝ f`, which is `C^p` at `x`, with the fixed
  continuous linear evaluation `ContinuousLinearMap.apply ℝ F a`, commutes it
  with the iterated derivative by
  `ContinuousLinearMap.iteratedFDeriv_comp_left`, and finishes with
  `iteratedFDeriv_succ_apply_right`. The fixed direction `a` occupies the last
  slot of the word, which is the first derivative taken.
- `orderedDerivativeFamilyNorm_lineDeriv`: if `ContDiffAt ℝ (p + 1) (f i) x` for
  every `i`, then the family indexed by `A × I` with component
  `fun y => fderiv ℝ (f i) y (v a)` at `(a, i)` has order-`p` norm equal to the
  order-`(p + 1)` norm of `f`. After the previous lemma, the equivalence
  `Fin.snocEquiv` matches pairs of a fixed direction index and a word of length
  `p` with all words of length `p + 1`, each exactly once; the sum is reordered
  by `Finset.sum_comm`. No symmetry of derivatives is used.

## Relation to the elliptic L² statement

The published `ConstantCoefficientEllipticL2EstimateStatement d r` uses, for
`F : EuclideanSpace ℝ (Fin d) → ℂ` and the standard orthonormal basis
`e = EuclideanSpace.basisFun (Fin d) ℝ`, the pointwise ordered top-derivative
tensor norm

`√(∑ w : Fin r → Fin d, ‖iteratedFDeriv ℝ r F x (fun j => e (w j))‖ ^ 2)`.

`orderedDerivativeFamilyNorm_euclidean_singleton d r G x` proves that
`orderedDerivativeFamilyNorm ⇑e r (fun _ : Unit => G) x` is exactly this
expression with `G` for `F`. Thus a singleton scalar family with canonical
Euclidean directions gives that norm with no dimension factor. This module does
not import the statement file and proves nothing about its estimate.

## Provenance and scope

This is an internal definition and helper unit, not a transcription of an
external theorem. Its convention is the tensor norm of C. B. Morrey and
L. Nirenberg, *On the analyticity of the solutions of linear elliptic systems of
partial differential equations*, Comm. Pure Appl. Math. 10 (1957), 271–290
(registered original
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`,
SHA-256 `61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`).
Their equation (2.1), printed page 275 / PDF page 5, takes the squared norm of a
tensor to be the sum of the squared absolute values of all its components, and
(2.2) forms the gradient tensor by adding one differentiation index per
derivative. Here the index `i` plays the role of the tensor's other indices and
the word `w` that of the differentiation indices, with arbitrary directions in
place of coordinate directions.

The unit serves as a prerequisite for a separate ordered-tensor bilinear Leibniz
inequality. It asserts no Leibniz estimate, elliptic estimate, analyticity or
automorphic conclusion.

Worker 94 authored the definitions, the helper results other than the two
singleton results, and the initial exposition. Worker 878 added
`orderedDerivativeFamilyNorm_unique` and
`orderedDerivativeFamilyNorm_euclidean_singleton`, checked the source
convention and revised this exposition.
