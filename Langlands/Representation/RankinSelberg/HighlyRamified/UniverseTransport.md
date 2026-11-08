# Moving gamma stability to smaller universes

Module `Langlands.Representation.RankinSelberg.HighlyRamified.UniverseTransport`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. The predicates
`PairStability.{uF, uV, uW} r t` and `UniformPairStability.{uF, uV, uW} r t` quantify
over candidate spaces in universe `uV` and test spaces in universe `uW`. The
adjacent-rank induction closes only when both spaces lie in one universe, so it
proves these predicates at a common universe. This module moves them down to any
smaller universes.

## Provenance

This is Lean bookkeeping with no counterpart in the literature. Jacquet and
Shalika 1985 do not track universes. The derivation is internal to this project.

## Definitions

- `uliftRepresentation ρ`: a representation `ρ` of `G` on `V`, moved to
  `ULift V` along `ULift.moduleEquiv`. So `g` acts by `ρ g` on the underlying
  vector.
- `uliftRepresentationEquiv ρ`: the equivalence of representations from `ρ` to
  `uliftRepresentation ρ`, given by `ULift.moduleEquiv.symm`.

## Lemmas

- `hasScalarCharacter_of_equiv e h`: if `ρ` has scalar character `ω` along
  `z : C →* G` (`Classification.HasScalarCharacter`) and `e : ρ ≃ τ`, then so does `τ`.
- `fixedVectors_ne_bot_of_equiv e h`: if `ρ` has a nonzero vector fixed by a
  subgroup `K`, then so does `τ`. The image `e v` of a nonzero fixed vector `v`
  is one.
- `sameGLCentralCharacter_of_equiv F e₁ e₂ h`: `SameGLCentralCharacter` passes
  along equivalences of both candidates.
- `hasPrincipalLevelVector_of_equiv F e h`: `HasPrincipalLevelVector F π m`
  passes along an equivalence.

## Main theorems

- `pairStability_of_ulift : PairStability.{uF, max uV uV', max uW uW'} r t →
  PairStability.{uF, uV, uW} r t`. Given data in universes `uV, uW`, apply the
  hypothesis to `uliftRepresentation` of `π₁, π₂, σ`. Genericity transfers by
  `Whittaker.isGeneric_iff_of_equiv`, the central-character condition by
  `sameGLCentralCharacter_of_equiv`. Gamma factors transfer by
  `IsPadicSymmetricGammaFactor.congr_equiv` along the twisted equivalences
  `Langlands.twistEquiv (χ ∘ det) e_i` and `e₃`. The bound `A` is the one for the
  lifted data.
- `uniformPairStability_of_ulift : UniformPairStability.{uF, max uV uV', max uW uW'}
  r t → UniformPairStability.{uF, uV, uW} r t`, the same argument with the same
  bound for given levels `m, m'`. Level vectors transfer by
  `hasPrincipalLevelVector_of_equiv`.
- `pairStability_of_common : PairStability.{uF, max uF uV uW, max uF uV uW} r t →
  PairStability.{uF, uV, uW} r t`. This is `pairStability_of_ulift` with
  `uV' = max uF uW` and `uW' = max uF uV`.
