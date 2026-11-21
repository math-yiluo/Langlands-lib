# Functions with vanishing derivative in a fixed tangent direction

Module `Langlands.Geometry.Manifold.ZeroDirectionalDerivative` (namespace
`Langlands.Geometry.Manifold.ZeroDirectionalDerivative`). Internal calculus used to show that the
differentials of the closed matrix realizations of `G(F ⊗ ℝ)` are jointly injective (module
`Langlands.Global.InfiniteAdelicChartFormula`). There is no literature source; the results are
the sum, product and quotient rules of manifold differentiation, packaged for one tangent vector.

## Setting

`M` is a charted space over `H` with model `I : ModelWithCorners ℝ E H`, `x : M` and
`X : TangentSpace I x`. `K` is a real normed commutative algebra (`NormedCommRing K`,
`NormedAlgebra ℝ K`).

## Declarations

- `ZeroDeriv X h` for `h : M → K`: there is `h' : E →L[ℝ] K` with
  `HasMFDerivAt I 𝓘(ℝ, K) h x h'` and `h' X = 0`.
- `zeroDeriv_const`: constant functions (derivative `0`, `hasMFDerivAt_const`).
- `ZeroDeriv.add`, `ZeroDeriv.mul`: sums and products (`HasMFDerivAt.add`, `HasMFDerivAt.mul`; the
  product derivative is `f x • g' + g x • f'`, which vanishes on `X`).
- `zeroDeriv_finset_sum`: finite sums, by induction on the finset.
- `zeroDeriv_aeval`: if every `f s` has `ZeroDeriv X`, so does
  `y ↦ MvPolynomial.aeval (fun s => f s y) P` for every multivariate polynomial `P` over a ring `R`
  with `Algebra R K` (induction on `P`: constants, sums, multiplication by a variable).
- `ZeroDeriv.congr`: the property depends only on the germ at `x`
  (`HasMFDerivAt.congr_of_eventuallyEq`).
- `ZeroDeriv.clm`: composition with a continuous real-linear map `L : K →L[ℝ] F` (chain rule).
- `ZeroDeriv.div`: for a normed field `𝕂` over `ℝ`, if `f` and `g` have `ZeroDeriv X`,
  `g x ≠ 0`, and `y ↦ f y / g y` is differentiable at `x`, then the quotient has `ZeroDeriv X`.
  *Proof.* Near `x` the product `(f / g) * g` equals `f`; the product rule and uniqueness of the
  derivative give `(f x / g x) * g' X + g x * q' X = f' X`, i.e. `g x * q' X = 0`, so `q' X = 0`.
- `hasMFDerivAt_finset_sum'`: the sum rule for finitely many functions into `K`.
- `zeroDeriv_of_mul_eq_one`: let `A B : M → Matrix n n K` with `A y * B y = 1` for all `y` and
  `A x = 1`. If the entries of `A` have `ZeroDeriv X` and the entries of `B` are differentiable at
  `x`, then the entries of `B` have `ZeroDeriv X`. *Proof.* Entry `(i, j)` of `A y * B y` is the
  constant `∑ k, A y i k * B y k j`; differentiating it at `x` (sum and product rules) and using
  `A x = 1` and the vanishing derivatives of `A` gives `b'_{ij} X = 0`.
