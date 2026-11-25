# Interior estimates for elliptic left-invariant word operators on a Lie group

This module defines left-invariant differential operators on a Lie group given by words in
finitely many tangent vectors at the identity. It also defines their commutative symbol and
states the interior estimate for the elliptic ones. It proves nothing; the statement
`LieGroupEllipticInteriorEstimateStatement` is a target for a separate proof.

## Setting

`E : Type u` is a real normed space and `H : Type v` is a group with a charted-space structure
modelled on `E` and a smooth Lie group structure `LieGroup 𝓘(ℝ, E) ∞ H`. The tangent space at the
identity is Mathlib's `GroupLieAlgebra 𝓘(ℝ, E) H`, which is `E` itself. Functions are
complex-valued. For a tangent vector `X` and a function `φ : H → ℂ`, the Library's
`groupDirectionalValue 𝓘(ℝ, E) X φ g` is `mvfderiv (fun h => φ (g * h)) 1 X`. This is the real
derivative of `φ` along the positive right orbit through `g`, i.e. the derivative of `φ` along the
left-invariant vector field of `X`.

## Definitions

Fix `X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H`.

- `lieWordDerivative X : FreeMonoid (Fin n) →* Function.End (H → ℂ)` is the monoid
  homomorphism `FreeMonoid.lift` of `i ↦ groupDirectionalValue 𝓘(ℝ, E) (X i)`. The word
  `[i₁, …, iₖ]` acts by `D_{X i₁} ∘ ⋯ ∘ D_{X iₖ}`: the last letter is applied first. The empty word
  acts as the identity. This is the order in which the product `X i₁ ⋯ X iₖ` of the enveloping
  algebra acts through an algebra homomorphism into endomorphisms.
- `lieWordAction X P φ`, for `P : MonoidAlgebra ℂ (FreeMonoid (Fin n))`, is the finite sum
  `∑_w P(w) • lieWordDerivative X w φ` over the support of the coefficient function `P.coeff`.
  It is a pointwise sum of functions and needs no smoothness of `φ`.
- `lieWordSymbol X ξ`, for a real linear form `ξ` on the tangent space at the identity, is the
  complex algebra homomorphism `MonoidAlgebra.lift` of the monoid homomorphism
  `FreeMonoid.lift (i ↦ (ξ (X i) : ℂ))`. It sends the word `[i₁, …, iₖ]` to
  `ξ (X i₁) ⋯ ξ (X iₖ)` and is multiplicative.

If every word of `P` has length `r`, the operator `lieWordAction X P` has order at most `r`.
`ξ ↦ lieWordSymbol X ξ P` is its principal symbol at the identity, without the factor `i^r`: in a
chart, `D_{X i₁} ⋯ D_{X iₖ}` has top-order part `D^k(X̃ i₁(x), …, X̃ iₖ(x))`, where `X̃ i` is the
left-invariant vector field of `X i` and `X̃ i(1) = X i`. Symbols at other points are pulled back
by the differentials of left translations, so a nonvanishing symbol at the identity means that
the operator is elliptic at every point.

## The statement

`LieGroupEllipticInteriorEstimateStatement` quantifies over the universes `u` of `E` and `v` of
`H`, a finite-dimensional `E`, a Lie group `H` as above, natural numbers `n` and `r`, vectors
`X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H` and two word combinations `Ptop` and `Plow`. It assumes:

1. every word in the support of `Ptop.coeff` has length exactly `r`;
2. every word in the support of `Plow.coeff` has length less than `r`;
3. ellipticity: `lieWordSymbol X ξ Ptop ≠ 0` for every nonzero real linear form `ξ` on the
   tangent space at the identity.

The conclusion holds for every word combination `Q`. There are a compact set `V ⊆ H` and a real
constant `C ≥ 0` with the following property. Let `φ : H → ℂ` be smooth
(`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ`) with `lieWordAction X (Ptop + Plow) φ x = 0` for every `x : H`.
Then for every real `M` with `‖φ x‖ ≤ M` for all `x ∈ V`,

`‖lieWordAction X Q φ 1‖ ≤ C * M`.

`V` and `C` depend on the data and on `Q`, but not on `φ`. This is the point of the statement: one
bound by the supremum of `|φ|` on a fixed compact set holds for all solutions of the equation at
once.

Degenerate cases are included. If `r = 0`, then `Plow = 0` and `Ptop` is a multiple `c • 1` of the
empty word. If moreover `E` is nonzero, ellipticity forces `c ≠ 0`, so the only solution is
`φ = 0`. If `E = 0`, every nonempty word acts by zero, and the estimate holds with `V = {1}`.

## Provenance

The statement is derived (not quoted from one source). In a chart around the identity the
operator `lieWordAction X (Ptop + Plow)` is a linear differential operator of order `r` with
smooth complex coefficients. By hypothesis 3 it is elliptic there. Morrey and Nirenberg, *On the
analyticity of the solutions of linear elliptic systems of partial differential equations*,
Comm. Pure Appl. Math. 10 (1957), Theorem C (printed p. 274), state the interior estimate for such
equations with `C^∞` coefficients. For a solution `u` with right-hand side `f = 0` in a bounded
domain `𝒟` and a compact subdomain `𝒜`, for every `p ≥ 0`, it gives
`∫_𝒜 ∑ |D^{r+p} u|² ≤ k_p ∫_𝒟 |u|²`, with `k_p` depending only on the equation and the domains.
Interior estimates of all orders, Sobolev's embedding, and transport through the chart
then give the conclusion. Here `V` is the preimage of a closed coordinate ball. The derivatives
of `Q φ` at `1` are derivatives of `φ` of order at most the length of the longest word of `Q`.

Harish-Chandra, *Two theorems on semi-simple Lie groups*, Ann. of Math. 83 (1966), §17,
Lemma 33 (printed pp. 108–109), uses the same kind of operator: the element `u = ω + 2ω_𝔨`,
written as the sum of squares of an orthonormal basis of the Lie algebra, and a monic polynomial
`v` in `u`. He states that they are elliptic differential operators on the group. The present
statement is the uniform quantitative form of that ellipticity, which the automorphic
application needs: Lemma 33 there concludes only analyticity.

The Library's `Langlands.Analysis` modules (Morrey–Nirenberg route, for example
`canonicalScalarWeightedFactorialBounds`) prove analyticity of solutions with analytic
coefficients. Their constants depend on the solution through its derivatives of order below the
order of the operator. They do not prove this statement.

## Use

`Langlands.Automorphic.GroupSchemeFunctions.AdelicAutomorphicUniformGrowthReductionStatement`
(module `GroupSchemeAutomorphicUniformGrowthReductionStatement`) uses the universes `u, u`
instance, on the infinite adelic points of a connected reductive group, to obtain uniformly
moderate growth of automorphic forms.
