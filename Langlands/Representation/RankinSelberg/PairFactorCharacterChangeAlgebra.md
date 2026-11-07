# Monomial transport of normalized functional equations

Lean module: `Langlands.Representation.RankinSelberg.PairFactorCharacterChangeAlgebra`.

This is an internal helper module for the proof of
`Langlands.RankinSelberg.PairFactorCharacterChangeStatement`. It has no
literature counterpart: it records the elementary bookkeeping that, when every
integral of one family equals a fixed nonzero monomial `α X^a` (in the spectral
variable `X = q^(-s)`) times an integral of another family, the Laurent spans of
their value sets agree and a normalized functional equation passes from one
family to the other with an explicitly changed epsilon monomial.

## Declarations

- `regularAt_C_mul_X_zpow_mul_iff`: for `z ≠ 0` and `c ≠ 0`,
  `RegularAt (C c * X^m * R) z ↔ RegularAt R z`. Proof: the monomial
  `C c * X^m` and its inverse `C c⁻¹ * X^(-m)` are regular at `z ≠ 0`
  (`regularAt_C`, `RegularAt.zpow`), and regularity is closed under products.

- `NormalizedFunctionalEquation.monomial_transport`: from
  `NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual`, nonzero units
  `α β`, integers `a b` with `m' + a = m - b` and `c' * α = c * β * q^(-b)`,
  it derives
  `NormalizedFunctionalEquation q P Pdual ζ c' e m' (C α * X^a * R) (C β * X^b * Rdual)`.
  Proof: regularity of the new continuations at `s` and `1 - s` gives
  regularity of the old ones (previous lemma); evaluation of a monomial multiple
  is `eval_C_mul_X_zpow_mul`; with `spectralPoint q (1 - s) = q^(-1) X(s)^(-1)`
  (`spectralPoint_sub_one_sub`) the old equation multiplied by
  `β X(1-s)^b` becomes the new equation, by a `linear_combination` with the
  monomial identity `β X(1-s)^b (c X^m) = c' X^m' (α X^a)`.

- `zetaSpan_values_eq_of_monomial`: two abstract integral families
  `I₁ : M₁ → M₁' → ℂ → ℂ` and `I₂ : M₂ → M₂' → ℂ → ℂ`, parametrized
  surjectively by vectors through `c₁, c₁', c₂, c₂'`, with a surjective vector
  map `T`, and with `I₂ (c₂ v) (c₂' w) s = α X(s)^a * I₁ (c₁ (T v)) (c₁' w) s`.
  Then the Laurent spans (`zetaSpan`) of their sets of rational continuations
  coincide. Proof: `zetaSpan_eq_of_monomial_mul`, using
  `HasRationalContinuation.monomial_mul` with `α X^a` in one direction and
  `α⁻¹ X^(-a)` in the other.

- `functionalEquation_transfer_of_monomial`: under the same monomial relation
  `hI` for the original integrals and an analogous relation `hD` (with `β X^b`
  and the same `T`) for the dual integrals, the clause "every pair has
  continuations satisfying the normalized functional equation with `P`, `Pdual`,
  `ζ`, `c`, `e`, `m`" transfers to the second family with `c'`, `m'` subject to
  `m' + a = m - b` and `c' α = c β q^(-b)`. Proof: choose preimages under the
  surjective parametrizations, take the old continuations, multiply by the
  monomials (`HasRationalContinuation.monomial_mul`), and apply
  `NormalizedFunctionalEquation.monomial_transport`.
