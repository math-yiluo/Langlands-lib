# Proof of the differentiated frozen principal estimate

This module proves the published proposition
`Langlands.Analysis.CoordinateScalarFrozenDerivativeEstimateStatement`
(module `Langlands.Analysis.CoordinateScalarFrozenDerivativeEstimateStatement`)
as the theorem

```text
Langlands.Analysis.coordinateScalarFrozenDerivativeEstimate (d r : ℕ) :
    CoordinateScalarFrozenDerivativeEstimateStatement E d r
```

for every real normed space `E` (implicit, with its given norm, in an
arbitrary universe `uE`) and all `d r : ℕ`, including `0`. It adds no
hypothesis. The bound therefore holds for every
`D : CoordinateScalarOperator E d r` with its actual basis and complex
coefficient functions, every freezing point `x₀`, every derivative order `p`
(including `0`), every open set `S`, coefficients and `u` that are
`ContDiffOn ℝ ∞` on `S`, and every `x ∈ S`. No equation, ellipticity,
analyticity, positivity or boundedness hypothesis is used.

The proof is internal elementary analysis by Worker 94. It is the
differentiated frozen-coefficient step of the Morrey–Nirenberg (1957) interior
route described in the Library note
`notes/automorphic/elliptic-analyticity-source-map.md`. That source estimates
the frozen-minus-actual operator difference with its own constants; the proof
here follows no printed argument line by line. It proves exactly the published
algebraic inequality.

## Imports

The module imports the statement module and two published proof modules:

- `Langlands.Analysis.OrderedDerivativeFamilyLeibnizProof`, for the theorem
  `orderedDerivativeFamilyLeibniz` (the binomial Leibniz bound for complete
  ordered derivative families of a bilinear product, task `250fdf1a`);
- `Langlands.Analysis.SmoothIteratedFDerivSymm` (Worker 815), for
  `iteratedFDeriv_append_of_contDiffOn` (nesting of iterated derivatives on an
  open set) and `contDiffOn_infty_iteratedLineDeriv` (smoothness of a
  fixed-word line derivative).

It also uses the lemmas published with `orderedDerivativeFamilyNorm`. The
target pair and its import closure are unchanged.

## Notation and private lemmas

Write `T_q(f)(x)` for `orderedDerivativeFamilyNorm v q (fun _ : Unit => f) x`,
the statement's norm. The private abbreviation `scalarTensorNorm` names it for
any finite direction type `A` and `v : A → E`. It equals the square root of
`∑_{w : Fin q → A} ‖iteratedFDeriv ℝ q f x (v ∘ w)‖²`. The private lemmas,
all stated for such an `A`, are:

1. `T_q` is nonnegative. `T_0(f)(x) = ‖f x‖`, and `T_q(-f) = T_q(f)`.
2. For a constant `a`, `T_{q+1}(a - f)(x) = T_{q+1}(f)(x)` when `f` is
   `C^{q+1}` at `x`. The derivative of the constant vanishes at positive
   order.
3. Triangle inequalities. `T_q(f + g) ≤ T_q(f) + T_q(g)` for `f`, `g` that are
   `C^q` at `x` (from `orderedDerivativeFamilyNorm_add_le`). Also
   `T_q(∑_{i∈s} f_i) ≤ ∑_{i∈s} T_q(f_i)` for a finite sum. This uses the
   linearity of `iteratedFDeriv` on finite sums, `WithLp.toLp_sum` and
   `norm_sum_le`.
4. Scalar Leibniz bound. Let `f`, `g` be `ContDiffOn ℝ ∞` on the open set `S`
   and `x ∈ S`. Then
   `T_p(f g)(x) ≤ ∑_{j=0}^{p} choose(p,j) T_j(f)(x) T_{p-j}(g)(x)`.
   This is `orderedDerivativeFamilyLeibniz` with singleton index types
   `I = J = Unit` and `B = ContinuousLinearMap.mul ℝ ℂ`. Its operator norm
   is `1` by `ContinuousLinearMap.opNorm_mul`.
5. Fixed-word line derivatives. Let `u` be `ContDiffOn ℝ ∞` on `S`, `x ∈ S`
   and `w : Fin k → A`. Then
   `T_p(y ↦ iteratedFDeriv ℝ k u y (v ∘ w))(x) ≤ T_{p+k}(u)(x)`. By
   `iteratedFDeriv_append_of_contDiffOn`, the `p`-th derivative of this
   function along `v ∘ z` equals `iteratedFDeriv ℝ (p+k) u x (v ∘ Fin.append z w)`.
   Each summand over `z` is at most the sum over all words `w'`, so the sum
   over `z` is bounded by the sum over pairs `(z, w')`. That double sum is
   the full sum over words of length `p + k`, via `Fin.appendEquiv`. The
   square root is monotone. No factor depending on `p`, `k` or the number of
   directions appears.
6. Combining 4 and 5, with `contDiffOn_infty_iteratedLineDeriv` for the
   smoothness of the line derivative:
   `T_p(a · ∂^k_w u)(x) ≤ ∑_{j=0}^{p} choose(p,j) T_j(a)(x) T_{p-j+k}(u)(x)`.
7. Frozen version. Apply 6 to the coefficient `y ↦ a x₀ - a y` and split off
   the `j = 0` summand with `Finset.sum_range_succ'`. That summand is
   `‖a x₀ - a x‖ T_{p+k}(u)(x)`. By lemma 2, every summand with index `j + 1`
   has `T_{j+1}(a x₀ - a) = T_{j+1}(a)`. This gives
   `‖a x₀ - a x‖ T_{p+k}(u)(x) + ∑_{j<p} choose(p,j+1) T_{j+1}(a)(x) T_{p-(j+1)+k}(u)(x)`.

## Main proof

Fix `D`, `S`, the coefficient smoothness, `u`, `x₀`, `p` and `x ∈ S`, and set
`v i = D.basis i`. Write `a_{k,w} = D.coefficient k w` and
`∂^k_w u(y) = iteratedFDeriv ℝ k u y (v ∘ w)`. The proof then defines:

- `V_w(y) = (a_{r,w}(x₀) - a_{r,w}(y)) ∂^r_w u(y)` for top words `w : Fin r → Fin d`;
- `H = ∑_w V_w`;
- `L(y) = ∑_{k : Fin r} ∑_w a_{castSucc k, w}(y) ∂^k_w u(y)`, the lower-order part.

By `Fin.sum_univ_castSucc`, `CoordinateScalarOperator.action` splits into
`L` plus its top-order part `∑_w a_{r,w}(y) ∂^r_w u(y)`. The definition of
`action` evaluates derivatives on the basis vectors `D.basis (w j)`, which
are `v ∘ w`. Distributing `sub_mul` and `Finset.sum_sub_distrib` then gives
the exact pointwise identity

```text
∑_w a_{r,w}(x₀) ∂^r_w u = (D.action u + H) + (-L).
```

All functions involved are `ContDiffOn ℝ ∞` on `S` (products and finite sums
of coefficients and fixed-word line derivatives), hence `C^p` at `x`, as the
triangle inequalities require. The chain of estimates is:

1. `T_p((D.action u + H) + (-L)) ≤ T_p(D.action u) + T_p(H) + T_p(L)`, using
   the triangle inequality twice and negation invariance;
2. `T_p(H) ≤ ∑_w T_p(V_w)` and `T_p(L) ≤ ∑_{k : Fin r} ∑_w T_p(a_{castSucc k,w} ∂^k_w u)`
   by the finite-sum triangle inequality;
3. private lemma 7 bounds each `T_p(V_w)`, and private lemma 6 bounds each
   lower term by
   `∑_{j=0}^{p} choose(p,j) T_j(a_{castSucc k,w})(x) T_{p-j+k}(u)(x)`;
4. `Finset.sum_add_distrib` and `Finset.sum_mul` move the factor
   `T_{p+r}(u)(x)` outside the sum of the top coefficient variations. After
   unfolding the abbreviation, the result is the right-hand side of the
   statement.

Natural-number subtraction in the derivative orders is Lean's truncated
subtraction, exactly as in the statement. When `p = 0`, `Finset.range p` is
empty. When `r = 0`, `Fin r` is empty.

## Checks

The theorem uses only `propext`, `Classical.choice` and `Quot.sound`. The
module compiles at the default heartbeat limit, with no `maxHeartbeats`
option. The theorem's only universe parameter is `uE`. The helper lemmas are
private and generalize the direction type to any finite type `A`.

## Scope

The theorem is only the algebraic frozen-action estimate at one point. It
does not prove weighted factorial bounds, elliptic estimates or analyticity.
