# Assembly of highly ramified gamma stability from generic gamma factors

Module `Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`
(Jacquet and Shalika 1985, Proposition 4.1, printed page 326). It proves no
stability itself. It shows that determinant twists keep the hypotheses of the
statement, and it rewrites the conclusion as an equality of the gamma factors
built by `genericSymmetricGammaFactor`. These facts are standard and are
implicit in Jacquet and Shalika's argument. They are derived here from Library
results. The source does not state them as separate lemmas.

## Twists keep the hypotheses

- `isGeneric_quasicharacter_twist_iff T ψ χ π`: let `T` be topological data for
  the p-adic field `F`, `ψ` a unitary additive character and `χ` a continuous
  quasicharacter of `Fˣ`. Then `π ⊗ (χ ∘ det)` is generic for `ψ` exactly when
  `π` is. Proof: `χ ∘ det` has open kernel, by `quasicharacter_isOpen_ker` and
  the continuity of the determinant `T.generalLinearDeterminant`. So
  irreducibility and admissibility carry over through `isIrreducible_twist_iff`
  and `isAdmissible_twist_iff`. A nonzero standard Whittaker functional carries
  over through the equivalence `determinantTwistFunctionalEquiv`, which keeps
  the underlying linear form.
- `isGeneric_quasicharacter_twist`: the forward direction.
- `hasGLCentralCharacter_twist χ h`: if `ρ` has central character `ω` on
  `GL_(n+1)`, then `ρ ⊗ (χ ∘ det)` has central character `ω · χ^(n+1)`, because
  `det (c · 1) = c^(n+1)`.
- `sameGLCentralCharacter_twist F χ h`: if `π₁` and `π₂` have the same central
  character (`SameGLCentralCharacter`), so do their twists by the same `χ ∘ det`.

## Conclusion as an equality of generic gamma factors

The section `Canonical` gives `F.Carrier` the local instance
`F.canonicalNormedField`. The Library's generic gamma factor results use this
instance. Its topology is definitionally `F.canonicalTopologicalData.topology`,
the topology of the target statement. The two instance paths agree only at
default transparency, so the proofs use explicit terms instead of `rw`.

- `exists_common_twist_gammaFactor_iff F ψ ν hπ₁ hπ₂ hσ χ`: take generic
  `π₁, π₂` of `GL_(r+1)`, generic `σ` of `GL_(t+1)` and a self-dual Haar measure
  `ν`. Then some `G` is a gamma factor (`IsPadicSymmetricGammaFactor`, with
  measure `ν.val`) of both twisted pairs `(π_i ⊗ (χ ∘ det), σ)` exactly when the
  two values of `genericSymmetricGammaFactor` for these pairs are equal. The
  genericity of each twist comes from `isGeneric_quasicharacter_twist`.
  Forward: `genericSymmetricGammaFactor_eq` identifies each constructed factor
  with `G`. Backward: take `G` to be the first constructed factor
  (`genericSymmetricGammaFactor_isPadic`). Then
  `isPadicSymmetricGammaFactor_iff_eq_genericSymmetricGammaFactor` shows that it
  is also the factor of the second pair.
- `exists_bound_common_twist_gammaFactor_iff`: for the same fixed data, the
  conclusion of `HighlyRamifiedGammaStabilityStatement` (there is `A` such that
  every `χ` with `A ≤ multiplicativeConductor χ` gives a common gamma factor)
  is equivalent to the same claim with the common factor replaced by equality of
  the two constructed generic gamma factors. Proof: apply the previous lemma
  under the quantifiers.
- `exists_bound_common_twist_gammaFactor_of_unique`: for the same fixed data,
  suppose there is `A` such that, for every `χ` with
  `A ≤ multiplicativeConductor χ`, any gamma factor `G₁` of the first twisted
  pair equals any gamma factor `G₂` of the second. Then the conclusion of the
  target holds with the same `A`. Proof: the two constructed factors
  (`genericSymmetricGammaFactor_isPadic`) are gamma factors of the two twisted
  pairs, so they are equal by hypothesis. The first therefore serves as the
  common factor.

## The target from its uniqueness form

`HighlyRamified.PairStability r t` is the uniqueness form of the target for
candidates of rank `r + 1` and tests of rank `t + 1`. It has the target's
quantifiers and hypotheses word for word: the additive conductor of `ψ` is `0`,
`π₁, π₂, σ` are generic, and `π₁, π₂` have the same central character. Its
conclusion: there is `A` such that, for every `χ` with
`A ≤ multiplicativeConductor χ`, any two gamma factors of the twisted pairs are
equal. The bound may depend on all the data.

`highlyRamifiedGammaStability_of_pairStability h` proves
`HighlyRamifiedGammaStabilityStatement.{uF, uV, uW}` from
`h : ∀ r t, PairStability.{uF, uV, uW} r t`. The proof introduces the target's
binders and applies `exists_bound_common_twist_gammaFactor_of_unique`. The
target's `letI := F.canonicalTopologicalData.topology` binders are accepted by
the lemma stated with the canonical normed-field instance, because the two
topologies are definitionally equal.

## The target from level-uniform stability

- `nontrivial_of_isGeneric T ψ hπ`: a generic representation acts on a
  nontrivial space. Its nonzero Whittaker functional would vanish on a zero
  space.
- `HighlyRamified.pairStability_of_uniformPairStability h` derives
  `PairStability r t` from `HighlyRamified.UniformPairStability r t`. The
  predicate `UniformPairStability` and the level predicate `HasPrincipalLevelVector` are
  defined in `Langlands.Representation.RankinSelberg.HighlyRamified.Uniform`.
  Genericity includes admissibility, hence smoothness, and the space is
  nontrivial. So `HighlyRamified.exists_hasPrincipalLevelVector` gives levels
  `m₁, m₂, m₃` for `π₁, π₂, σ`. By `HasPrincipalLevelVector.mono`, both candidates have
  level `max m₁ m₂`. The uniform bound for the levels `max m₁ m₂` and `m₃` is
  the required `A`.
- `highlyRamifiedGammaStability_of_uniformPairStability` combines the two
  previous results: level-uniform stability for all ranks proves the target.

So a proof of the target needs only the uniqueness form of the stability bound,
or equivalently a conductor bound for equality of the constructed generic gamma
factors of the twists. The per-data equivalences use only genericity of
`π₁, π₂, σ`. They do not use the additive conductor of `ψ` or the central
characters. Those hypotheses are needed only for the stability bound itself.
