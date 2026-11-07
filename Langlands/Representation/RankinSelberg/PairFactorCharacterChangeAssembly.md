# Assembly of the unequal-rank character-change statement

Lean module: `Langlands.Representation.RankinSelberg.PairFactorCharacterChangeAssembly`.

This module assembles the proof of
`Langlands.RankinSelberg.PairFactorCharacterChangeStatement`, the conjunction of
`UnequalRankLPolynomialCharacterChangeStatement` and
`UnequalRankEpsilonCharacterChangeStatement` (Cogdell and Piatetski-Shapiro
1994, Lemma 2.1 and its proof, printed pages 161–163, for the JPSS relations
with self-dual measures). The analytic content of the epsilon half, the
transport of one functional equation from `ψ` to `ψ^a(x) = ψ(a x)` for fixed
functionals, is isolated in the Prop `FixedFunctionalEpsilonTransport`. This
module only does the bookkeeping around it. That bookkeeping is internal; it
does not follow any step of the printed proof.

All declarations are for a p-adic field `F` with its canonical topological data,
the induced local-field instances, and Borel measurable structures on `F`,
`GL_(n+1)(F)`, the upper unipotent group and the quotient
`LeftUnipotentQuotient n F`. Throughout, `q` is the residue cardinality, the
absolute value is `normalizedAbsoluteValue`, and `N = (r+1)(n+1)`.

## Declarations

- `unequalRankLPolynomialCharacterChange`: the L-polynomial half,
  `UnequalRankLPolynomialCharacterChangeStatement.{uF, uV, uW}`. Proof: the
  Library theorem `Padic.isPadicSymmetricLPolynomial_characterChange`, which
  states that the symmetric L-polynomial relation for `ψ` and for `ψ.scale a`
  are equivalent. The irreducibility, admissibility and `r ≠ t` hypotheses are
  not used.

- `FixedFunctionalEpsilonTransport F hnr π σ ωπ ωσ ψ ν ν' a` (a Prop, `n < r`,
  `π` on `GL_(r+1)(F)`, `σ` on `GL_(n+1)(F)`): for every compatible quotient
  measure `μ`, all functionals `ℓ` for `(ψ, π)` and `ℓ'` for `(ψ, σ)` (not
  necessarily nonzero), and every `c`, `m`, the equation
  `UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m` implies that for
  some unit `c'` with
  `c' = c ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)` the equation
  `UnequalRankEpsilonEquation hnr q (ψ.scale a) abv μ ν' π σ ℓ_a ℓ'_a c' (m + N ord a)`
  holds, where `ℓ_a = characterChangeFunctional ψ π a ℓ` and
  `ℓ'_a = characterChangeInverseFunctional ψ σ a ℓ'` are the translated
  functionals. The complex power is `Complex.cpow` of the real number
  `normalizedAbs a`.

- `val_ne_zero_of_linearEquiv`: a linear equivalence of submodules sends an
  element with nonzero underlying vector to one with nonzero underlying vector.

- `normalizedAbs_cpow_ne_zero`: `|a|^z ≠ 0` for every complex `z`, because
  `|a| = (sqrtNormalizedAbs F a)^2 > 0` (`sqrtNormalizedAbs_sq`,
  `sqrtNormalizedAbs_pos`) and `Complex.cpow_eq_zero_iff`.

- `isUnequalRankEpsilonFactor_characterChange_of_transport`: given
  `FixedFunctionalEpsilonTransport F hnr π σ ωπ ωσ ψ ν ν' a` and
  `IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e`, the pair `e' = (c', m')`
  with `c' = e.1 ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)` and
  `m' = e.2 + N ord a` satisfies
  `IsUnequalRankEpsilonFactor hnr q (ψ.scale a) abv ν' π σ e'`. Proof: the
  measure clause is unchanged. Nonzero functionals for `ψ.scale a` are the
  images of the given nonzero functionals for `ψ` under
  `characterChangeFunctionalEquiv` and `characterChangeInverseFunctionalEquiv`.
  For the universal clause, nonzero functionals `ℓ`, `ℓ'` for `ψ.scale a` are
  pulled back along the inverse equivalences to nonzero functionals for `ψ`.
  The given relation supplies their equation with `(e.1, e.2)`, and the
  transport gives the equation for `ℓ`, `ℓ'` (by `apply_symm_apply`). The unit
  it produces equals `c'` because both have the same underlying complex number.

- `FixedFunctionalEpsilonTransportStatement` (a Prop at universes
  `uF, uV, uW`): `FixedFunctionalEpsilonTransport` holds for every p-adic field,
  every `n < r`, all representations `π` on a carrier in `uV` and `σ` on a
  carrier in `uW` with central characters `ω_π`, `ω_σ` (in the sense of
  `Classification.HasGLCentralCharacter`), every additive character `ψ`, all
  Haar measures `ν`, `ν'` and every unit `a`, provided `ν' = κ • ν` for some
  `κ ≥ 0` with `κ^2 = |a|`.

- `unequalRankEpsilonCharacterChange_of_transport`: the transport statement at
  universes `uF, uV, uW` and at `uF, uW, uV` gives
  `UnequalRankEpsilonCharacterChangeStatement.{uF, uV, uW}`. Proof: by
  `SelfDualHaar.val_eq_scale` (module `PairFactorCharacterChangeMeasures`) and
  `AdditiveHaarMeasure.scale_measure`, the self-dual measures satisfy
  `ν' = κ • ν` with `κ = sqrtNormalizedAbs F a`, and `κ^2 = |a|` by
  `sqrtNormalizedAbs_sq`. If `t < r`, `IsPadicSymmetricEpsilonFactor` is the
  unequal-rank relation for `(π, σ)` (`isPadicSymmetricEpsilonFactor_of_le`,
  `isPairEpsilonFactor_of_lt`; `IsPadicPairEpsilonFactor` unfolds to
  `IsPairEpsilonFactor`), and the previous theorem applies with the first
  transport hypothesis. If `r < t`, it is the relation for `(σ, π)`
  (`isPadicSymmetricEpsilonFactor_of_lt`). The previous theorem then applies to
  `(σ, π, ω_σ, ω_π)` with the second hypothesis, since the larger carrier is now
  in `uW`. Its exponent `(t+1)(r+1) ord a` and coefficient
  `ω_σ(a)^(r+1) ω_π(a)^(t+1) |a|^(-(t+1)(r+1)/2)` match the target after
  commuting the factors (`Nat.mul_comm`, `ring`).

- `pairFactorCharacterChange_of_transport`: the two transport statements give
  `PairFactorCharacterChangeStatement.{uF, uV, uW}`, as the conjunction of the
  two previous halves.
