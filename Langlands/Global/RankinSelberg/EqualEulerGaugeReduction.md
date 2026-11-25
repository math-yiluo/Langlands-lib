# The equal-rank partial Euler factorization from the Whittaker–Schwartz bound

Module `Langlands.Global.RankinSelberg.EqualEulerGaugeReduction`. The
proof reuses the published reduction `equalEulerFactorizationReduction`.

## Content

The module contains, in the namespace `Langlands.Global.RankinSelbergGlobal`:

- the statement `EqualEulerGaugeReductionStatement.{u, uQ}`, a `Prop`-valued definition:
  `EqualWhittakerSchwartzStatement.{u} → EqualEulerFactorizationStatement.{u, uQ}`;
- the theorem `equalEulerGaugeReduction`, which proves it;
- three theorems with other premises:
  - `equalEulerFactorization_of_gauge` assumes the primal gauge premise
    `EqualWhittakerGaugeIntegrable F T T'` for every number field `F` with compact adele
    quotient, every `r` and every pair of cuspidal realizations `T`, `T'` of `GL_(r+1)`.
    It concludes `EqualEulerFactorizationStatement.{u, uQ}`.
  - `equalEulerFactorization_of_equalUnfoldingGauge` assumes
    `EqualUnfoldingGaugeStatement.{u}`. It concludes `EqualEulerFactorizationStatement.{u, uQ}`.
  - `equalEulerFactorization_of_whittakerSchwartzGauge` assumes
    `WhittakerSchwartzGaugeStatement.{u}`. It concludes
    `EqualEulerFactorizationStatement.{u, uQ}`.

None of these proves `EqualEulerFactorizationStatement` outright. Each premise is a Library
statement; `EqualUnfoldingGaugeStatement` and `WhittakerSchwartzGaugeStatement` are proved in
the Library (see Provenance).

### The premises

- `EqualWhittakerSchwartzStatement` (module `EqualGaugeReduction`) says the following for
  every number field `F` with compact adele quotient, every `r` and every cuspidal
  realization `T` of `GL_n`, `n = r + 1`. There is a `C ≥ 0` such that for every standard
  additive character `ψ`, every vector `x` of `T`, every Schwartz–Bruhat function `Φ` and
  every real `σ > C`, the integral
  `∫_(N_n(𝔸) \ GL_n(𝔸)) |W_x^ψ(g)| |Φ(e_n g)| |det g|^σ dg` is finite.
  Here `W_x^ψ = cuspWhittaker F T ψ x` and the measure is `whittakerQuotientMeasure`.
- `EqualWhittakerGaugeIntegrable F T T'` (module `EqualUnfoldingReduction`) is premise G of
  the equal-rank unfolding (Cogdell 2004, p.211). There is a `C ≥ 0` such that
  `g ↦ W_x^ψ(g) φ_(x')(g) Φ(e_n g) |det g|^s` is integrable over `N_n(F) \ GL_n(𝔸)`
  whenever `Re s > C`. The bound is uniform over standard `ψ`, vectors `x`, `x'` and
  Schwartz–Bruhat `Φ`.
- `EqualUnfoldingGaugeStatement` is the conjunction of G and its dual G̃ for all equal-rank
  pairs. Only the first conjunct is used here.
- `WhittakerSchwartzGaugeStatement` is the general Whittaker–Schwartz estimate for analytic
  decay classes whose functions share a central-power exponent.

## Proof

`equalEulerFactorization_of_gauge` repeats the proof of the published
`equalEulerFactorizationReduction` (module `EqualEulerFactorizationReduction`). Fix `F`,
the unitary character `ψ`, `T`, `T'`, the Satake presentations `P`, `P'` and the finite set
`S`. Three inputs that the reduction took as hypotheses now come from Library theorems:

- The spherical factorization (A) is `UnramifiedWhittaker.unramifiedWhittakerFactorization`.
- The one-place cell decomposition (B) is `whittakerCellDecomposition`.
- The integrability bound `C₀` comes from the premise G for the pair `(T, T')` through
  `integrable_equalWhittakerIntegrand_of_gauge`. That theorem gives
  integrability of `equalWhittakerIntegrand F W W' Φ s` over `N_n(𝔸) \ GL_n(𝔸)` for
  `Re s > C₀`, uniformly over standard characters. The proof applies it to the standard
  character `ψ.complex` (`isStandardAdditiveCharacter_of_unitary`). Before, this bound came
  from the integrability clause of `EqualUnfoldingStatement`.

The proof then proceeds as in `equalEulerFactorizationReduction`:

1. It takes the abscissa `σ₂` of `exists_partialEulerFactor_convergence` and the uniform
   Satake bounds `C`, `C'` of `exists_hasSatakeBound_presentation`. The half-plane is
   `Re s > max(C₀, max(σ₂, localRadius r C C'))`.
2. The one-place step `EqualEulerReduction.setIntegral_insert`, applied to (A) and (B),
   gives `∫_(U_(A∪{v})) f = L(s, Π_v × Π'_v) ∫_(U_A) f` for finite `A ⊇ S` and `v ∉ A`.
3. The exhaustion theorem `integral_eq_hasProd_mul_setIntegral` then gives the equality
   `∫ f = L^S(s, Π × Π') · ∫_(U_S) f` (rewritten by
   `partialEqualWhittakerIntegral_eq_setIntegral` and commuted).

`equalEulerGaugeReduction` applies `equalEulerFactorization_of_gauge` to
`equalGaugeReduction h`. That theorem gives G for every pair from the Whittaker–Schwartz
bound of the first realization, together with the central-power bound of the second cusp
form. `equalEulerFactorization_of_equalUnfoldingGauge` applies
`equalEulerFactorization_of_gauge` to the first conjunct. The final theorem,
`equalEulerFactorization_of_whittakerSchwartzGauge`, is `equalEulerGaugeReduction` applied
to `equalGaugeSpecialization h`. All the theorems use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

This is an internal reduction for the proof of `EqualEulerFactorizationStatement`. Cogdell
2004 (*Analytic theory of L-functions for GL_n*, §2.3, printed p.210, with Theorem 3.3,
p.215) shows that for `Re s ≫ 0` the global integral is the integral over the places in `S`
times the unramified local factors. On p.210 Cogdell states without proof that the unfolded
integral over `N_n(𝔸) \ GL_n(𝔸)` converges for `Re(s) ≫ 0`. The factorization needs that
convergence. Cogdell argues with factorizable Whittaker functions. The steps here are derived from the Library statements and proofs
named above.

The premise `EqualWhittakerSchwartzStatement` isolates the one analytic estimate the proof
still needs. Its general form `WhittakerSchwartzGaugeStatement` is proved in the Library
(`whittakerSchwartzGauge`, module `WhittakerSchwartzGauge`). The premise G is the first half of
`EqualUnfoldingGaugeStatement`, proved in the Library (`equalUnfoldingGauge`, module
`EqualUnfoldingGauge`).
The reduction has the same form as the Library precedent
`EqualDualEulerFactorizationReductionStatement`: a `Prop`-valued implication, with a theorem
that proves it.
