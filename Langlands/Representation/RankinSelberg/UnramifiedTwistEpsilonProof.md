# Unramified twists of pair epsilon factors

Author: Worker 4803. Module
`Langlands.Representation.RankinSelberg.UnramifiedTwistEpsilonProof`. The
theorem `Langlands.RankinSelberg.unramifiedTwistEpsilon` proves
`UnramifiedTwistEpsilonStatement.{uF, uV, uW}` (module `UnramifiedTwistStatement`)
with the standard axioms only. The field universe and the two carrier universes
stay independent. The module has no new statement. Its helpers are in namespace
`Langlands.RankinSelberg.UnramifiedEpsilonTwist`. The scalar lemmas are in
`Langlands.RankinSelberg`.

The statement: let `χ(x) = |x|^u` and let `e = (c, m)` with
`ε(s, π × σ, ψ) = c q^(-ms)`, read with the larger rank first. Then
`e' = (c q^(-mu), m)` is the epsilon factor of `(π, σ ⊗ |det|^u)` and of
`(π ⊗ |det|^u, σ)`. The proof keeps every p-adic field, additive character,
self-dual measure, rank and rank order. It assumes no irreducibility and does
not prove that epsilon factors exist.

## How the proof goes

This proof copies the published proof of the gamma statement
(`UnramifiedTwistGammaProof`, `UnramifiedTwistGammaCertificates`,
`UnramifiedTwistGammaAssembly`) and uses its integral identities. The epsilon
relation also fixes the two normalized generators `P` and `Pdual`, so they have
to be transported too.

Throughout, `χ₁` and `χ₂` are characters of `F^×` that are trivial at `-1` and
satisfy `χ₁(x) χ₂(x) = |x|^u`. The first member of the pair is twisted by
`χ₁ ∘ det` and the second by `χ₂ ∘ det`. `Q_u` is the published unit
`spectralShiftUnit q hq u`, with value `q^(-u)`, and `R ↦ R(Q_u X)` is the
published `rationalRescale`.

### Scalar lemmas

- `epsilonMonomial_shift`: `epsilonMonomial q (c Q_u^m) m s =
  epsilonMonomial q c m (s + u)`. This follows from the published
  `spectralPoint_add`.
- `eval_spectralRescale`: `P(Q_u X)` evaluated at `q^(-s)` equals `P` at
  `q^(-(s+u))`.
- `NormalizedFunctionalEquation.shift`: if the normalized functional equation
  holds for `(P, Pdual, ζ, c, e, m, R, Rdual)`, it holds for
  `(P(Q_u X), Pdual(Q_(-u) X), ζ, c Q_u^m, e, m, R(Q_u X), Rdual(Q_(-u) X))`.
  The denominator conditions transfer exactly by the published
  `spectralRescale_denom_ne_zero_iff`. The rational values are computed by
  `spectralRescale_eval`. Then the original equation at `s + u` is applied,
  using `1 - s - u = 1 - (s + u)`. This parallels the published
  `GammaFunctionalEquation.shift`.

### Fixed functionals

Fix functionals `L` for `π` and `L'` for `σ`. The twisted representations get
`UnramifiedGammaTwist.functional`, which has the same underlying linear map.

- `equal_values` and `unequal_values`: for the twisted pair, the forward
  rational value set is the image of the original set under
  `rationalRescale Q_u`. In the unequal-rank case this holds for every
  rectangular block `(j, k)`. Every model vector is `modelMap v`
  (`modelMap_surjective`). The published `equal_forward` and `unequal_forward`
  write each twisted integral as the original integral at `s + u`.
  `HasRationalContinuation.shift` and `hasRationalContinuation_shift_iff` then
  give both inclusions.
- `equal_dual_values` and `unequal_dual_values` do the same for the dual value
  sets, with `Q_(-u)`. They use the published `equal_dual` and `unequal_dual`:
  the dual integrals move from `s` to `s - u`.
- `equal_equation` and `unequal_equation` transport the fixed-functional epsilon
  equation from `(c, m)` to `(c Q_u^m, m)`:
  - the minus-one scalar `ζ` is kept (`UnramifiedGammaTwist.minusOne`, since
    `χ₂(-1) = 1`);
  - the generators become `P(Q_u X)` and `Pdual(Q_(-u) X)`, by the value-set
    identities and the published `IsNormalizedGenerator.rescale`;
  - for each pair of model vectors (and each Schwartz–Bruhat function `Φ` in
    the equal-rank case), the Fourier partner `Φhat` is kept, the
    continuations are rescaled, and `NormalizedFunctionalEquation.shift`
    supplies the equation.

### Complete relations

- `equal_factor` and `unequal_factor`: the relations
  `IsEqualRankEpsilonFactor` and `IsUnequalRankEpsilonFactor` move from `e` to
  `(e.1 Q_u^(e.2), e.2)`. The existence of a compatible measure is kept. Nonzero
  functionals are twisted with the same linear map. An arbitrary functional of
  a twisted representation is untwisted by the published `untwistFunctional`,
  which keeps its linear map, and the original relation is applied to it. This
  is the argument of the published `equal_factor_of_equation`.
- `pair_factor`: `IsPairEpsilonFactor` by cases on the ranks, using
  `isPairEpsilonFactor_of_lt`, `isPairEpsilonFactor_self` and
  `not_isPairEpsilonFactor_of_lt`.
- `pair_both`: put `χ₂ = 1` or `χ₁ = 1`. `χ(-1) = 1` holds by the published
  `character_neg_one`, and `Langlands.twist_one` removes the trivial twist.
- `padic_pair_both`: the version for `IsPadicPairEpsilonFactor`, with the
  canonical residue cardinality, normalized absolute value and Borel
  structures. `shiftedValue F u e` abbreviates the transported value.
- `padic_symmetric_both`: `IsPadicSymmetricEpsilonFactor` in both rank orders.
  In the reversed order the two twist positions are swapped.
- `shiftedValue_fst`: the coefficient of `shiftedValue F u e` is
  `c q^(-(m u))`, by Mathlib's `Complex.cpow_int_mul`.

`unramifiedTwistEpsilon` applies `padic_symmetric_both` to `ν.val`. Its witness
is `e' = shiftedValue F u e`. The exponent is unchanged by definition, and
`shiftedValue_fst` gives the coefficient.

## Provenance

This is an internal derived proof of the published statement. Its literature
sources are recorded in `UnramifiedTwistStatement.md`:

- Henniart (1993), §4.4, printed p. 349 (`henniart-1993-epsilon-pairs`):
  `ε(π × (π_ρ ⊗ |det|^u), s, ψ) = ε(π × π_ρ, s + u, ψ)`.
- Jacquet, Piatetski-Shapiro and Shalika (1983) (`jpss-1983-rankin-selberg`):
  the integrals (2.4), printed p. 387; the functional equation (2.7)(iii),
  printed pp. 390–391; and the larger-rank-first convention (2.12), printed
  p. 403.

The proof uses only the published definitions and the published integral
identities. Henniart cites the "elementary properties" of epsilon factors
without an argument, so the proof is not taken from a text.
