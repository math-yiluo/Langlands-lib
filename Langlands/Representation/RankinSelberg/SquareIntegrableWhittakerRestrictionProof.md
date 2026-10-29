# The square-integrable Whittaker restriction-square estimate

Author: Worker 381.

This module proves the Library statement
`Langlands.RankinSelberg.SquareIntegrableWhittakerRestrictionStatement.{uF,uV}`
(module `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionStatement`):

```lean
theorem squareIntegrableWhittakerRestriction :
    SquareIntegrableWhittakerRestrictionStatement.{uF, uV}
```

The statement is formula (7) of JPSS 1983 §8.3. Fix a prime `p`, a `p`-adic
field `F` with topological data `T`, `n k : ℕ`, a right-invariant
`unipotentHaar`, a measure `μ` on `N_(n+1) \ GL_(n+1)(F)` compatible with
`generalLinearHaar` and `unipotentHaar`, a character `ψ`, and an irreducible
representation `π` of `GL_r(F)`, `r = n + (0 + k + 1) + 1`, with
`T.IsSquareIntegrable π`. For every `ℓ` and every vector `f` of the
coefficient model, the function

`N g ↦ ‖W_f(diag(g, 1_(k+1)))‖² · |det g|^(-(k+1))`

is integrable against `μ`. Every quantifier of the statement is kept,
including `n = 0`, `k = 0`, `ℓ = 0` and `f = 0`. The proof uses only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Proof

The theorem is a single term:

```lean
SquareIntegrableWhittakerRestriction.of_squareIntegrableWhittakerTorusSum
  squareIntegrableWhittakerTorusSum
```

It combines two results.

- `Langlands.RankinSelberg.SquareIntegrableWhittakerRestriction.of_squareIntegrableWhittakerTorusSum`,
  in the helper module
  `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionReduction`
  of this candidate, derives the statement from the torus lattice
  square-summability `SquareIntegrableWhittakerTorusSumStatement.{uF,uV}`. It
  does the measure theory. It writes `μ` as a countable sum over torus
  exponents `λ` of pushforwards of Haar measure on `K = GL_(n+1)(𝒪)`, using
  the published `quotientIwasawaIntegration` and `iwasawaTorusSum`. It bounds
  the integrand on each compact orbit, using a finite cover of `K` by
  translates of an open subgroup that fixes `W_f` on the right. Finally it
  identifies the weight `δ_(n+1)(λ)⁻¹ |det ϖ^λ|^(-(k+1))` with the inverse
  modulus of `diag(ϖ^λ, 1_(k+1))` in `GL_r`. Its Markdown gives the
  argument step by step.
- `Langlands.RankinSelberg.squareIntegrableWhittakerTorusSum`, published in
  `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumProof`,
  proves that torus lattice square-summability from `T.IsSquareIntegrable π`.
  This is the bridge from square-integrable matrix coefficients modulo the
  centre to square-summable Whittaker functions on the torus lattice. This
  candidate imports it and does not reprove it.

## Provenance

The target is formula (7) of Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), §8.3,
pp. 449–450. The source's premise is that `W` is square-integrable modulo
`N_r Z_r` (p. 449). With the integration formula (1) it deduces formula (2),
a weighted integral over `N_(r-1) \ G_(r-1)`. It then obtains (7), an
integral over `N_t \ G_t`, by applying the integration formula (6) to (2).
This proof takes a different route and uses none of (1), (2) and (6). It
combines the torus lattice square-summability, a measure-free counterpart of
square-integrability modulo `N_r Z_r`, with the Iwasawa decomposition of the
quotient measure on `N_t \ G_t`. The Reduction module's Markdown describes
this route.
