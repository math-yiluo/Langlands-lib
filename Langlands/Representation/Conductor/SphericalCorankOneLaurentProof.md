# Proof of the convergence and Laurent clauses for the spherical functions

Author: Worker 8. All declarations are in `Langlands.Conductor`. The module
proves two propositions with no premises, over every nonarchimedean local field
of any characteristic:

```lean
theorem unramifiedCorankOneLaurent : UnramifiedCorankOneLaurentStatement.{uF, uV}

theorem sphericalCorankOneLaurent : SphericalCorankOneLaurentStatement.{uF, uV}
```

- `UnramifiedCorankOneLaurentStatement`
  ([`UnramifiedCorankOneLaurentStatement`](UnramifiedCorankOneLaurentStatement.md)):
  for every `x`, every nonzero inverse-character functional `ℓ'` on `I(x)` and
  every `W`, `W'` in the two Whittaker models, if `Ψ(s, W, W')` converges on a
  right half-plane then `Ψ(s, W, W') ∏_i P(x_i q^(-s))` is a Laurent polynomial
  in `q^(-s)` on a right half-plane (JPSS 1983, Theorem (3.1)(ii)).
- `SphericalCorankOneLaurentStatement`
  ([`SphericalCorankOneLaurentStatement`](SphericalCorankOneLaurentStatement.md)):
  the first three conjuncts of the published
  `SphericalLFactorGenerationStatement`, namely the standard L-polynomial `P`,
  convergence of `Ψ(s, w, W_x)` and its Laurent numerator, for every `x`.

Notation: `W_x = inverseSphericalWhittaker h.conductor.1 h.uniformizer q x`,
`Ψ(s, W, W') = corankOneIntegral ψ abv μ W W' s`, `X = spectralPoint q s`.

## The proofs

**`unramifiedCorankOneLaurent`.** The bridge
`unramifiedCorankOneLaurent_of_multiplicativity hL hG`
([`UnramifiedCorankOneLaurentFromMultiplicativity`](UnramifiedCorankOneLaurentFromMultiplicativity.md))
applied to the two published proofs of JPSS 1983, Theorem (3.1), for
unramified principal series over every nonarchimedean local field:

- `hL := Langlands.RankinSelberg.localFieldPrincipalSeriesLFactorMultiplicativity`
  ([`LocalFieldPrincipalSeriesLFactorMultiplicativityProof`](../RankinSelberg/LocalFieldPrincipalSeriesLFactorMultiplicativityProof.md)),
  part (ii);
- `hG := Langlands.RankinSelberg.localFieldPrincipalSeriesGammaMultiplicativity`
  ([`LocalFieldPrincipalSeriesGammaMultiplicativityProof`](../RankinSelberg/LocalFieldPrincipalSeriesGammaMultiplicativityProof.md)),
  part (i).

**`sphericalCorankOneLaurent`.** Fix the data of the statement.

1. `P`, `IsCharacterLPolynomial … 1 π P` and the convergence clause come from
   the published `sphericalCorankOneConvergence`
   ([`SphericalCorankOneConvergenceProof`](SphericalCorankOneConvergenceProof.md)).
2. For the Laurent clause at `w` and `x`, the published
   `exists_perm_monotone_norm` gives a permutation `σ` with `x ∘ σ` norm-ordered.
3. The published `laurent_of_ordered`
   ([`SphericalLFactorGenerationReduction`](SphericalLFactorGenerationReduction.md))
   at `x ∘ σ` takes the Laurent statement (`unramifiedCorankOneLaurent`) and
   Jacquet's Lemma 2 with the normalization of the spherical image
   (`orderedUnramifiedWhittakerRealization`,
   [`OrderedUnramifiedWhittakerProof`](OrderedUnramifiedWhittakerProof.md)).
   It needs convergence of `Ψ(s, w, W_(x ∘ σ))`; this is the convergence
   clause at `x`, rewritten by `W_(x ∘ σ) = W_x`
   (`inverseSphericalWhittaker_comp_perm`).
4. Its conclusion at `x ∘ σ` is the Laurent clause at `x`, after rewriting by
   `W_(x ∘ σ) = W_x` and `∏_i P(x_(σ i) X) = ∏_i P(x_i X)`
   (`prod_comp_perm`).

These are the same steps as the first two clauses of the published
`sphericalLFactorGeneration_of_ordered`, with its premises replaced by their
proofs.

## Source

JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), Theorems (2.7) and
(3.1); Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`),
section 1, printed pages 517-519. The linked files give the details of each
input.
