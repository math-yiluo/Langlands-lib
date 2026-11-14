# Proof of the pair gamma twist exchange

Author: Worker 389.

The theorem `Langlands.RankinSelberg.pairGammaTwistExchange.{uF, uV, uW}` proves the
unchanged Library proposition `Langlands.RankinSelberg.PairGammaTwistExchangeStatement`
at three independent universe levels. For every p-adic field `F`, unitary additive
character `ψ`, additive Haar measure `ν`, ranks `r + 1` and `t + 1` in either order,
representations `π` and `σ` on complex modules, character `χ : Fˣ →* ℂˣ` and rational
function `G`, a symmetric p-adic gamma certificate of `(π ⊗ χ∘det, σ)` is the same as one
of `(π, σ ⊗ χ∘det)`. No hypothesis beyond those of the statement is added. The proof uses
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The helper declarations are in `Langlands.RankinSelberg.PairGammaTwistExchange`. The
integral identities they use are in the paired module `PairGammaTwistExchangeIntegrals`.
In this module the candidate has rank `r + 1` and the test rank `n + 1`.

## Implemented proof

**Rational algebra.** `gammaEquation_scale`: if `GammaFunctionalEquation q ζ e G R Rd`
holds, then `GammaFunctionalEquation q (ζ a) e G R (C κ · Rd)` holds for any unit `a` with
`a^e = κ`. Multiplying by a nonzero constant creates no poles and removes none
(`denom_eval_const_mul_ne_zero_iff`), so the equation holds on the same domain.
`gammaEquation_scale_one` is the case `a^e = 1`, with `Rd` unchanged.
`sign_exponent_val` and `sign_exponent_self` give the complex forms
`(χ(-1)^(n+1))^r = χ(-1)^((n+1)(r-n))` for `n ≤ r`, and `(χ(-1)^(n+1))^n = 1`.

**Fixed functionals, unequal rank** (`unequal_equation`, `n < r`). Take a Whittaker
functional `ℓ` of `π`, an inverse Whittaker functional `ℓ'` of `σ`, any quotient measure
`μ` and any `ν`. Then `UnequalRankGammaEquation` for `(π ⊗ χ, σ)` with
`(twisted ℓ, ℓ')` holds if and only if it holds for `(π, σ ⊗ χ)` with `(ℓ, twisted ℓ')`.
The coefficient maps are surjective onto their models (`modelMap_surjective`), so every
model vector is reached. Then:

- the forward integrals are equal (`unequal_forward`), so the nonzero-continuation sets of
  every block agree (`unequal_values`) and the same continuation `R` serves on both sides;
- the dual integrals differ by `c = χ(-1)^((n+1)(r-n))` (`unequal_dual`) and `c² = 1`, so
  the dual continuation becomes `C c · Rd` in both directions
  (`hasRationalContinuation_const_mul`);
- the minus-one scalar of the test changes from `ζ` to `ζ · χ(-1)^(n+1)`
  (`minusOne_twist`, resp. `minusOne_untwist` in the reverse direction). The exponent of
  `ζ` in the equation is `r`, and `(χ(-1)^(n+1))^r = c`, so `gammaEquation_scale` gives the
  equation with `C c · Rd` and the same `G`.

**Fixed functionals, equal rank** (`equal_equation`, `r = n`). The forward and dual
integrals agree for every Schwartz–Bruhat function (`equal_forward`, `equal_dual`), so the
same Fourier partner `Φhat` and continuations `R`, `Rd` serve on both sides, and the value
sets agree (`equal_values`). The minus-one scalar changes by `χ(-1)^(n+1)`, whose `n`-th
power is `1`, so `gammaEquation_scale_one` applies.

**Full relations.** `unequal_factor` and `equal_factor` keep the compatible-measure clause
verbatim. Nonzero functionals are carried by `twisted` / `untwisted`, which keep the
underlying linear map and hence nonvanishing. For every compatible quotient measure and
every pair of nonzero functionals, the equation on the target side is obtained by applying
the hypothesis to the transported functionals and then the fixed-functional equivalence.
Here `twisted (untwisted L)` is `L` definitionally.

**Rank branches.** `pair_factor` splits `IsPairGammaFactor` into three cases. For `n < r` it
uses `isPairGammaFactor_of_lt` and `unequal_factor`. For `r = n` it substitutes the
equality and uses `isPairGammaFactor_self` and `equal_factor`. For `r < n` both sides are
false (`not_isPairGammaFactor_of_lt`). `padic_pair` installs the canonical topology,
valuative relation, local-field structure and Borel measurable structures of
`IsPadicPairGammaFactor`. It then applies `pair_factor` with the normalized absolute value
and residue cardinality.

**Entry theorem.** `pairGammaTwistExchange` unfolds `IsPadicSymmetricGammaFactor`, whose
rank test `t ≤ r` is the same on both sides. If `t ≤ r`, it applies `padic_pair` to
`(π, σ)`. Otherwise both sides put `σ` first, and `padic_pair` applied to `(σ, π)`, read
backwards, gives the claim.

## Provenance and limits

This is an internal derivation from the JPSS integral definitions. It is not a numbered
theorem of H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. 105 (1983), 367–464 (`jpss-1983-rankin-selberg`). The relevant
conventions are in (0.3), printed p. 376 (PDF 11); (2.1), printed pp. 385–386 (PDF 20–21);
(2.4), printed p. 387 (PDF 22); and Theorem (2.7)(iii), printed p. 391 (PDF 26). The
statement's Markdown gives the source fingerprint and the sign derivation. The proof
generalizes the Library proof of `RankOneGammaTwistStatement` (`RankOneGammaTwistProof`) and
follows its structure. No analytic existence theorem, multiplicativity or stability result
is used. The theorem transports a supplied certificate in either direction. It does not
assert that a gamma factor exists.
