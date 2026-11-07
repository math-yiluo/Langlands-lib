# The unequal-rank pair-factor character change

Lean module: `Langlands.Representation.RankinSelberg.PairFactorCharacterChangeProof`.

This module proves the exact target
`Langlands.RankinSelberg.PairFactorCharacterChangeStatement.{uF, uV, uW}`: for
unequal ranks, in either order, the L-polynomial is unchanged and epsilon
certificates transform as stated when the additive character is replaced by
`ψ^a(x) = ψ(a x)` and the self-dual measure is changed accordingly (Cogdell and
Piatetski-Shapiro 1994, Lemma 2.1, printed pages 161–163). The module only
supplies the p-adic measure laws to the generic theorem
`UnequalRankEpsilonEquation.characterChange` (module
`PairFactorEpsilonTransport`) and applies the assembly
`pairFactorCharacterChange_of_transport` (module
`PairFactorCharacterChangeAssembly`).

The module uses the local instances of `PairFactorCharacterChangeAssembly`
(canonical topological data of the p-adic field, Borel measurable structures on
`F`, `GL_(n+1)(F)`, the upper unipotent group and the quotient
`LeftUnipotentQuotient n F`), so that its statements are the ones defined
there. It adds local instances that make the quotient and the rectangular
matrix spaces Borel, and that record the second countability and σ-compactness
of `F` from the canonical topological data.

## Declarations

- `fixedFunctionalEpsilonTransport`:
  `FixedFunctionalEpsilonTransportStatement.{uF, uV, uW}`. Fix a p-adic field,
  `n < r`, representations with central characters `ω_π` and `ω_σ`, `ψ`, Haar
  measures with `ν' = κ • ν` and `κ^2 = |a|`, a compatible quotient measure `μ`,
  functionals `ℓ`, `ℓ'` and an equation
  `UnequalRankEpsilonEquation hnr q ψ abv μ ν π σ ℓ ℓ' c m`. The new coefficient
  `c' = c ω_π(a)^(n+1) ω_σ(a)^(r+1) |a|^(-N/2)` is a unit, since `|a|^z ≠ 0`
  (`normalizedAbs_cpow_ne_zero`). The equation for `ψ.scale a`, `ν'`,
  `ℓ_a`, `ℓ'_a`, `c'` and `m + N ord a` is `UnequalRankEpsilonEquation.characterChange`
  with the following inputs:
  - `q > 0`, from `residueCardinality_gt_one`;
  - `|a| = q^(-ord a)`, from `normalizedAbs_of_ne_zero`;
  - the character-change law of `μ`, from the Library theorem
    `characterChangeCompatibleMeasure`;
  - the right invariance of `μ`, from `IsCompatible.right_invariant`;
  - the rectangular character-change law of every product measure, from
    `characterChangeRectangularProductStatement`;
  - the right-scaling law of every product measure, the first half of
    `padic_rectangular_laws`.

  The σ-finiteness of `ν` follows from σ-compactness of `F`.

- `pairFactorCharacterChange`: `PairFactorCharacterChangeStatement.{uF, uV, uW}`,
  by `pairFactorCharacterChange_of_transport` applied to
  `fixedFunctionalEpsilonTransport` at universes `uF, uV, uW` and at
  `uF, uW, uV`.
