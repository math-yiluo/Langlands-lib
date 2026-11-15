# Weighted lexicographic monomial orders

For a linearly ordered type of variables `σ` with `WellFoundedGT σ` and a weight
`w : σ → ℕ`, `weightLex w : MonomialOrder σ` is the monomial order on `σ →₀ ℕ` that
compares monomials first by their weight `Finsupp.weight w a = Σ_s a s * w s` and breaks ties
with the lexicographic order `Lex (σ →₀ ℕ)`. For the constant weight `1` this is Mathlib's
`MonomialOrder.degLex`.

## Construction

- `WeightLex w` is a type synonym of `σ →₀ ℕ`. `toWL w : (σ →₀ ℕ) ≃+ WeightLex w` is the
  identity.
- `key w f = toLex (weight w f, toLex f)` lies in `Lex (ℕ × Lex (σ →₀ ℕ))`. It is injective
  (`key_injective`), and the linear order on `WeightLex w` is pulled back along it
  (`LinearOrder.lift'`).
- `toWL_lt_iff` / `toWL_le_iff` unfold the order: `a < b` iff `weight a < weight b`, or the
  weights are equal and `toLex a < toLex b`.
- The order is compatible with addition (`IsOrderedCancelAddMonoid`), because the weight is
  additive and `Lex (σ →₀ ℕ)` is an ordered cancellative monoid.
- It is well founded (`WellFoundedLT`) when `σ` is `WellFoundedGT`, as the inverse image of
  the well-founded lexicographic order on `ℕ × Lex (σ →₀ ℕ)`. Mathlib's `Finsupp.Lex`
  well-foundedness requires `WellFoundedGT σ`.
- `weightLex w` packages these into a `MonomialOrder σ`. `toSyn_monotone` holds because
  `a ≤ b` pointwise implies `weight a ≤ weight b` and `toLex a ≤ toLex b`.
- `weightLex_lt_iff` states the order relation `≺[weightLex w]` in these terms.

## Provenance

This is internal infrastructure for the proof of `NilpotentConeIdealStatement`. The
construction copies `Mathlib/Data/Finsupp/MonomialOrder/DegLex.lean` with
`Finsupp.weight w` in place of the total degree. Weighted orders refined by a
lexicographic order are standard (Cox–Little–O'Shea, *Ideals, Varieties, and Algorithms*,
Ch. 2 §2 exercises; Ch. 8 §4).
