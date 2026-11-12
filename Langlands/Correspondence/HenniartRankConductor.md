# Conductors of the extension of the stable images

Author: Worker 4803. Module `Langlands.Correspondence.HenniartRankConductor`, namespace
`Langlands.Henniart.Extension`. A supporting module of `HenniartSurjectivityStepProof`;
it defines no statement. Its hypotheses are published Library statements passed as
arguments; nothing is assumed globally.

## Main result

`rankExtension_conductor`: assume

- `hSC : LocalFactor.ConductorExponent.SpectralConductorStatement.{uK, uW} K` (Tate
  (3.4.5), Deligne (5.5.2): `ε(V, s) = ε(V, 0) q^(-(a(V) + n(ψ) dim V) s)` for a local
  constant system, with `a(V)` read at any finite inertia presentation),
- `hBHK : RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0}` and
  `hJPSS : Conductor.ConductorExponentStatement.{uK, uV}`,
- a geometric reciprocity candidate `e`, a local-constant system `ε` for a
  reciprocity family `eC`, and `hS : StableExistsAt K (k+1)`.

Then for every Weil class `σ` of rank `k + 1` with Artin conductor `a`
(`Numerical.HasArtinConductor K σ a`), `Numerical.conductor K (rankExtension K hS σ) = a`.

## Proof

Write `σ = z · b₀` and `rankExtension K hS σ = z · π₀` with `π₀` the stable image of
`b₀` (`rankExtensionBasis_spec`). Choose a candidate `Φ` for `b₀`, an additive character
`ψ` (`padicUnitaryAdditiveCharacterExists`) and a measure `ν` self-dual for `ψ` (the first
clause of `PairFactorCompatibility`). `Φ` sends the trivial rank-one Weil class to the
trivial class of `GL₁` (`candidate_character_generator`), so one certificate `(c₀, m₀)`
is the epsilon factor of `b₀ ⊗ 1` and of `π₀ × 1` (`candidate_pairEpsilon`).

- Weil side, `weil_exponent_of_twist`: the unramified twist law
  (`arithmeticPairUnramifiedTwist`, published) moves the certificate of `b₀ ⊗ 1` to one
  of `σ ⊗ 1` with the same exponent `m₀`. Then `exponent_of_isArithmeticPairEpsilonFactor`
  gives `m₀ = a + n(ψ)(k+1)`. That lemma unfolds `IsArithmeticPairEpsilonFactor`: the
  pair epsilon value of the bottom-field data `(A, B)` is the value of `A ⊗ B ≅ A`
  (`B` is the restriction of the trivial character: `tensorCharacterLineEquiv`,
  `twistOneEquiv`), a zero-monodromy pair, so it is `conditionalDeligneValue` of the
  class of `A`. The Artin presentation of `σ` transports to the restriction of `A`
  along an equivalence with the same conductor (`exists_presentation_of_equiv`, from
  `artinConductorOfQuotient_equiv`). `hSC` then gives the value `D q^(-(a + n(ψ₁) r) s)`,
  where `n(ψ₁) = n(ψ)` for the bottom-field character `ψ₁` (`additiveConductor_base_eq`,
  from `PadicField.ConductorTransport.additiveConductor_eq`) and `r = k + 1` is the rank.
  Comparing with `c₀ q^(-m₀ s)` at all `s` gives the exponent
  (`exponent_eq_of_monomial`, at `s = 0` and `s = 1`).
- Side of `GL_(k+1)`, `conductor_eq_of_pairEpsilon`: twisting `π₀` by `χ ∘ det` keeps
  the exponent `m₀` (`isSupercuspidalPairEpsilonFactor_unramifiedTwist_left`, from the
  published `RankinSelberg.unramifiedTwistEpsilon`). The lemma
  `exists_newvectorConductor_of_pairEpsilon` (module `HenniartConductorFinitenessProof`,
  which is part of this contribution and is not yet in the Library; it uses `hBHK` and
  `hJPSS`) gives a newvector conductor `b = m₀ - (k+1) n(ψ)`, and a
  newvector conductor is the first fixed level
  (`firstFixedLevel_eq_of_isNewvectorConductor`).

Hence the conductor of `z · π₀` is `m₀ - (k+1) n(ψ) = a`.

## Provenance

Internal. Henniart (1988), Théorème 1.2 (printed p. 498, PDF p. 3) asks for conductor
preservation. The two conductor identities used are Tate (1979), (3.4.5) (printed p. 15)
and Deligne (1973), (5.5.2) (printed p. 548) on the Weil side, and
Jacquet–Piatetski-Shapiro–Shalika (1981), Théorème (5.1) (printed p. 211) with
Bushnell–Henniart–Kutzko (1998), introduction (printed p. 703), on the side of `GL_n`,
each through its published Library statement.
