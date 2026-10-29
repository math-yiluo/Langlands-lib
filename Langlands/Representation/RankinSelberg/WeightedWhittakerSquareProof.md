# The weighted Whittaker square estimate

Author: Worker 724. The helper module
`Langlands.Representation.RankinSelberg.WeightedWhittakerSquareReduction`
contains three lemmas copied from Worker 676's published module
`Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof` (see
that module's Markdown).

This module proves the Library statement
`Langlands.RankinSelberg.WeightedWhittakerSquareStatement.{uF,uV}`
(module `Langlands.Representation.RankinSelberg.WeightedWhittakerSquareStatement`):

```lean
theorem weightedWhittakerSquare : WeightedWhittakerSquareStatement.{uF, uV}
```

Fix a prime `p`, a `p`-adic field `F` with supplied topological data `T`,
`n : ℕ`, a unitary additive character `ψ`, a right-invariance instance for
`unipotentHaar`, a measure `μ` on `N_(n+1) \ GL_(n+1)(F)` compatible with
`generalLinearHaar` and `unipotentHaar`, and an irreducible representation `π`
of `GL_(n+1)(F)` on `V : Type uV` with `T.IsSquareIntegrable π`. The theorem
gives both conjuncts of the statement. For every `ℓ : glFunctionals ψ n π`,
every vector `f` of its coefficient model, every Schwartz–Bruhat function `Φ`
and every real `a > 0`, the function

```
fun q => (whittakerNorm ψ f.val q) ^ 2 * ‖Φ (quotientLastRow n q)‖ ^ 2 *
  (quotientDeterminantAbs (normalizedAbsoluteValue T) n q) ^ (2 * a)
```

is integrable for `μ`. The same holds for every `ℓ : glInverseFunctionals ψ n π`
with `inverseWhittakerNorm` in place of `whittakerNorm`.

Every binder of the statement is kept: every prime, every supplied `T`, every
rank `n + 1` including rank one, every compatible `μ`, every `ψ`, independent
universes `uF` and `uV`, and zero functionals, vectors and Schwartz–Bruhat
functions. The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The theorem is one term:

```lean
weightedWhittakerSquare_of (fun F T m => recursiveQuotientIntegration F T m)
  squareIntegrableWhittakerRestriction
```

It combines three results.

- `Langlands.RankinSelberg.weightedWhittakerSquare_of`, in the helper module
  `Langlands.Representation.RankinSelberg.WeightedWhittakerSquareReduction`
  submitted with this module. It proves the statement from two hypotheses:
  `h1`, the recursive quotient integration formula
  `RecursiveQuotientIntegrationStatement F T m` at all `p`, `F`, `T`, `m`, and
  `h2`, the restricted Whittaker square estimate
  `SquareIntegrableWhittakerRestrictionStatement.{uF,uV}`. The helper's
  Markdown `WeightedWhittakerSquareReduction.md` describes that proof
  section by section.
- `Langlands.RankinSelberg.recursiveQuotientIntegration`, published in module
  `Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof`.
  It proves `RecursiveQuotientIntegrationStatement F T n` for every `p`, `F`,
  `T` and `n`. The lambda only makes its implicit prime and instance binders
  match those of `h1`.
- `Langlands.RankinSelberg.squareIntegrableWhittakerRestriction`, published in
  module
  `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionProof`.
  It proves `SquareIntegrableWhittakerRestrictionStatement.{uF,uV}`.

## Route

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
Section 8.3, printed p. 449 (the equal-rank argument). The implemented route,
detailed in the helper Markdown, is as follows.

- Rank one (`n = 0`). Every element of `GL_1` is central, so the unitary
  central character supplied by square integrability makes `|W|` constant.
  The integrand is then bounded by a geometric tail over determinant slices of
  the quotient, which is finite because right translation by the uniformizer
  preserves `μ` and the order-zero slice lies in the image of the compact group
  `GL_1(O)`. Neither `h1` nor `h2` is used.
- Rank `m + 2`. Formula (1) (`h1`) writes `μ` as the pushforward of
  `(μ_(m+1) × d^×t × dk)` with density `|det g|⁻¹` under the coordinates
  `diag(g,1) · t · k`. The integrand is bounded by a product of a function of
  `g` and a function of `t`. The `g`-factor is a finite sum, over the integral
  orbit of the vector, of the integrands of formula (2) (`h2` at `k = 0`). The
  weight `|det g|^(2a)` is absorbed by a support bound: a Whittaker function of
  a smooth vector vanishes at `diag(g,1)` when `|det g|` is large. This bound
  replaces the gauge step of the source. The `t`-factor is a geometric tail.
- Inverse character. It is the standard character of `ψ(-x)`, so the inverse
  clause is the standard clause for `ψ.scale (-1)`, transferred by
  `Integrable.congr`.
