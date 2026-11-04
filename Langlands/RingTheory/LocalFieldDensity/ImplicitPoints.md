# Points of submersive presentations over complete normed fields

Author: Worker 712.

This internal helper module applies the inverse function theorem to
submersive presentations over a complete nontrivially normed field. It is a
derived result: it combines Mathlib's inverse function theorem
(`HasStrictFDerivAt.map_nhds_eq_of_equiv`), Mathlib's submersive presentations
(`Algebra.SubmersivePresentation`), and the polynomial calculus helper
`Langlands.AlgebraicGeometry.PointManifold.polynomialDerivative`. It cites no
literature. Its only consumer is the density module
`Langlands.RingTheory.LocalFieldDensity.Density`. All declarations are in the
namespace `Langlands.RingTheory.LocalFieldDensity`.

## Declarations

- `hasStrictFDerivAt_polynomial_eval`: for a nontrivially normed field `K`, a
  finite index type `ι`, `p : MvPolynomial ι K` and `x : ι → K`, the map
  `y ↦ eval y p` has strict Fréchet derivative `polynomialDerivative p x` at
  `x`. The proof is by polynomial induction (constants, sums, multiplication by
  a variable). It uses the analytic constant, sum, product and coordinate rules,
  and the product identity `polynomialDerivative_mul`. The published helper
  proves the ordinary Fréchet derivative; this lemma gives the strict
  derivative, which the inverse function theorem needs.
- `eq_zero_of_eventually_eval_eq_zero`: over a nontrivially normed field, a
  polynomial in finitely many variables that vanishes on a neighbourhood of a
  point `t₀` is zero. Some ball of radius `ε` around `t₀` lies in the
  vanishing set. In the sup metric this ball is the product of the coordinate
  balls `ball (t₀ i) ε`. Each of these balls is infinite, since it is a
  neighbourhood in a nontrivially normed field. Mathlib's
  `MvPolynomial.funext_set` shows that a polynomial vanishing on a product of
  infinite sets is zero.
- `pointOfSolution P v hv`: for a presentation `P` of a `K`-algebra `S` and a
  vector `v : ι → K` at which all relations of `P` vanish, the `K`-point
  `S →ₐ[K] K` sending each generator `P.val i` to `v i`. It is built by
  `AlgHom.liftOfSurjective` from `aeval v` on the polynomial ring. That map
  kills the kernel of `aeval P.val` because the kernel is the ideal spanned by
  the relations. `pointOfSolution_val` records the value on generators.
- `FreeVar P`: for a pre-submersive presentation, the subtype of variables
  outside `Set.range P.map`. These are the free variables, the ones not paired
  with a relation.
- `eventually_exists_algHom`: let `K` be complete and nontrivially normed, let
  `P : Algebra.SubmersivePresentation K S ι σ` have finitely many variables and
  relations, and let `x : S →ₐ[K] K`. For every `t : FreeVar P → K`
  sufficiently close to the free coordinates `fun i => x (P.val i)` of `x`,
  some `y : S →ₐ[K] K` has `y (P.val i) = t i` for every free variable `i`.

## Proof of `eventually_exists_algHom`

Let `v₀ i = x (P.val i)`. All relations vanish at `v₀`, since `x` kills them
in `S`. Define

```text
Φ : (ι → K) → (σ ⊕ τ → K),   Φ v = Sum.elim (j ↦ eval v (P.relation j)) (i ↦ v i),
```

where `τ = FreeVar P`. By `hasStrictFDerivAt_polynomial_eval` and
`hasStrictFDerivAt_apply`, and componentwise by `hasStrictFDerivAt_pi'`, `Φ`
has strict derivative `D` at `v₀`. The components of `D` are
`polynomialDerivative (P.relation j) v₀` and the coordinate projections onto
the free variables.

`D` is injective. Let `D h = 0`. The free components give `h i = 0` for every
free `i`. The relation components then say that the square matrix
`(eval v₀ (pderiv (P.map k) (P.relation j)))_{j,k}` sends
`(h (P.map k))_k` to zero. The sum over all variables is reindexed along the
injective map `P.map` (`Fintype.sum_of_injective`), because the free terms
vanish. This matrix is the transpose of the image of `P.jacobiMatrix` under
`eval v₀`. Its determinant is `x P.jacobian`, which is a unit because
`P.jacobian` is a unit in `S`. So `Matrix.eq_zero_of_mulVec_eq_zero` gives
`h (P.map k) = 0` for all `k`, hence `h = 0`.

Both sides have dimension `card ι`, since `σ ⊕ τ ≃ ι` via the range of
`P.map` and its complement. So `D` is a continuous linear equivalence `f'`
(`LinearMap.linearEquivOfInjective`). The inverse function theorem
`HasStrictFDerivAt.map_nhds_eq_of_equiv` shows that `Φ` maps neighbourhoods
of `v₀` onto neighbourhoods of `Φ v₀`. In particular `Set.range Φ` is a
neighbourhood of `Φ v₀`.

The continuous map `g t = Sum.elim 0 t` sends the free coordinates of `v₀` to
`Φ v₀`. Hence `g t ∈ Set.range Φ` for all `t` near those coordinates. If
`Φ v = g t`, then all relations vanish at `v` and `v i = t i` for each free
`i`. The point `pointOfSolution P v _` is the required `y`.
