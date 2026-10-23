# Pair factors after highly ramified twists

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
the stability and vanishing properties of local factors of pairs under twists
by highly ramified characters, from Jacquet and Shalika, *A Lemma on Highly
Ramified ε-Factors*, Math. Ann. 271 (1985), 319-332. The factors are the
relations `IsPadicSymmetricGammaFactor`, `IsPadicSymmetricEpsilonFactor` and
`IsPadicSymmetricLPolynomial` of the module `PadicPairFactors`, which cover
both rank orders. The module defines `SameGLCentralCharacter` and four
statements, none of them proved.

## Source

Jacquet--Shalika 1985 (printed page = PDF page + 318).

- **Section 1.1, printed page 319.** `F` is a nonarchimedean local field, `G_r`
  is `GL(r, F)`, and `ψ` is a nontrivial additive character of `F`. "For
  convenience" the largest ideal on which `ψ` is trivial is the ring of
  integers. For an irreducible admissible `π`, `L(s, π) = P(q^{-s})^{-1}` with
  `P ∈ ℂ[x]` and `ε(s, π, ψ) = c q^{-fs}` (display (1)). If `π₁` and `π₂` have
  the same central character and `χ` is a multiplicative character of conductor
  `𝔓^a`, then (display (2)) `L(s, π₁ ⊗ χ) = L(s, π₂ ⊗ χ) = 1` and
  `ε(s, π₁ ⊗ χ, ψ) = ε(s, π₂ ⊗ χ, ψ)` once `a` is large enough. For `π` on
  `G_r` and `σ` on `G_t` the factors `L(s, π × σ)` and `ε(s, π × σ, ψ)` "have
  the property analogous to (2)", and the paper proves this (Section 4).
- **(4.1), printed page 326.** For irreducible generic `π` and `σ`,
  `γ(s, π × σ, ψ) = ε(s, π × σ, ψ) L(1 - s, π̃ × σ̃)/L(s, π × σ)` (display (1)).
  **Proposition.** Suppose `π_i` (`i = 1, 2`) and `σ` are irreducible generic
  representations of `G_r` and `G_t`, and `ω_{π₁} = ω_{π₂}`. There is an
  integer `A` such that if `χ` is a character of `F^×` with conductor `𝔓^a`,
  `a ≥ A`, then `γ(s, (π₁ ⊗ χ) × σ, ψ) = γ(s, (π₂ ⊗ χ) × σ, ψ)` (display (2)).
  The proof reduces `t < r - 1` and `t > r` to other ranks through induced
  representations (printed page 327).
- **(5.1) Proposition, printed page 331.** Let `π` and `σ` be irreducible
  generic representations of `G_r` and `G_t`. If `a` is large enough and `χ`
  has conductor `𝔓^a`, then `L(s, (π ⊗ χ) × σ) = 1`.
- **(5.2) Remark, printed page 331.** The factors are also defined for
  nongeneric `π` and `σ`, and Propositions 5.1 and 4.1 hold for all pairs.
  This extension is not stated here.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data,
`ψ` is a `UnitaryAdditiveCharacter` of `F`, `ν` is in the published
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`, and the
ranks are `r + 1` (the twisted representations) and `t + 1` (the fixed `σ`),
in either order. Representations are actual representations of `GL_{m}(F)` on
complex vector spaces, the twisted ones in universe `uV` and `σ` in universe
`uW`.

The factor relations come from `PadicPairFactors`. For `t ≤ r`,
`IsPadicSymmetricGammaFactor F ψ ν (π ⊗ χ) σ G` is the pair relation
`IsPadicPairGammaFactor` with candidate `π ⊗ χ` and test `σ`; for `r < t` it
is the pair relation with candidate `σ` and test `π ⊗ χ`. The epsilon and L
relations are defined the same way, over `IsPadicPairEpsilonFactor` and
`IsPadicPairLPolynomial`. The L relation requires a compatible quotient
measure and asks, for every one, that `P` be the normalized generator of the
JPSS zeta values, so `L(s, π × σ) = 1/P(q^{-s})`, and `P = 1` says
`L(s, π × σ) = 1`.

`SameGLCentralCharacter F π₁ π₂`: some homomorphism `ω : Fˣ →* ℂˣ` satisfies
the published `Classification.HasGLCentralCharacter` for both `π₁` and `π₂`,
i.e. every scalar matrix `z·1` acts on both by `ω(z)`.

The three statements quantify over every prime `p`, every `F`, `ψ` and `ν` as
above with `F.canonicalTopologicalData.additiveConductor ψ = 0`, and all `r`
and `t`. Throughout, `χ` is a published `Quasicharacter F` (a continuous
homomorphism `Fˣ → ℂˣ`), and `π ⊗ χ` is the published
`Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) π`, the action
`g ↦ χ(det g) π(g)`.

`HighlyRamifiedGammaStabilityStatement` (Proposition 4.1): for `π₁`, `π₂` of
`GL_{r+1}(F)` and `σ` of `GL_{t+1}(F)` with `Whittaker.IsGeneric ψ r π₁`,
`Whittaker.IsGeneric ψ r π₂`, `Whittaker.IsGeneric ψ t σ` and
`SameGLCentralCharacter F π₁ π₂`, there is `A : ℕ` such that for every `χ` with
`A ≤ F.canonicalTopologicalData.multiplicativeConductor χ` some rational
function `G` satisfies `IsPadicSymmetricGammaFactor F ψ ν.val (π₁ ⊗ χ) σ G`
and `IsPadicSymmetricGammaFactor F ψ ν.val (π₂ ⊗ χ) σ G`.

`HighlyRamifiedLVanishingStatement` (Proposition 5.1): for `π` of
`GL_{r+1}(F)` and `σ` of `GL_{t+1}(F)` with `Whittaker.IsGeneric ψ r π` and
`Whittaker.IsGeneric ψ t σ`, there is `A : ℕ` such that for every `χ` with
conductor exponent at least `A`,
`IsPadicSymmetricLPolynomial F ψ ν.val (π ⊗ χ) σ 1`.

`HighlyRamifiedEpsilonStabilityStatement` (the pair analogue of display (2) of
Section 1.1 for the ε-factor): the hypotheses of the gamma statement, and the
conclusion that some `e : ℂˣ × ℤ` satisfies
`IsPadicSymmetricEpsilonFactor F ψ ν.val (π₁ ⊗ χ) σ e` and
`IsPadicSymmetricEpsilonFactor F ψ ν.val (π₂ ⊗ χ) σ e`. The witness `e = (c, m)`
encodes `ε(s) = c q^{-ms}`, as in the published epsilon relation.

`HighlyRamifiedStabilityStatement` is the conjunction of the three statements.

## Interpretation

- **Conductors.** Jacquet and Shalika's standing assumption that `ψ` is trivial
  exactly on the ring of integers is `additiveConductor ψ = 0`: the published
  `additiveConductor` is Tate's `n(ψ)`, the largest `n` with `ψ(ϖ^{-n} O) = 1`.
  "`χ` has conductor `𝔓^a`" is `multiplicativeConductor χ = a`, the least unit
  level on which `χ` is trivial (`0` exactly for unramified `χ`). Their bound
  `a ≥ A` is kept literally. Their `A` is an integer; `A : ℕ` loses nothing,
  since the conductor exponent is a natural number.
- **Characters and twists.** A "character of `F^×`" is a quasicharacter
  (continuous, not necessarily unitary); the proof of 5.1 reduces to unitary
  ones. The twist `π ⊗ χ` is again irreducible, admissible and generic. That
  is not a hypothesis of the statements; the Library transfers the Whittaker
  functionals (`determinantTwistFunctionalEquiv`).
- **Central characters.** `SameGLCentralCharacter` asks for one `ω` acting by
  scalars on both representations. An irreducible admissible representation
  has a central character (Schur's lemma), so this is `ω_{π₁} = ω_{π₂}`.
  Continuity of `ω` is not required.
- **Rank order.** Jacquet and Shalika treat all ranks `r` and `t`; the cases
  `t < r - 1` and `t > r` reduce to others (printed page 327). They use the
  JPSS convention (2.12) that the factors of a pair are read with the larger
  rank first. The symmetric relations implement this convention: when
  `t ≤ r` they are the pair relations for `(π ⊗ χ, σ)`, and when `r < t` for
  `(σ, π ⊗ χ)`. So the statements cover all ranks.
- **Genericity.** `Whittaker.IsGeneric ψ m τ` is irreducibility,
  admissibility and a nonzero Whittaker functional for the standard character
  of `ψ`. The relations pair the `ψ`-functionals of the representation of
  larger rank with the `ψ̄`-functionals of the other, as in JPSS.
  `Whittaker.characterChangeFunctionalEquiv` at `a = -1`, together with
  `standardCharacter_scale_neg_one`, gives a linear equivalence to the
  inverse-character functional space. It preserves nonzero functionals, so
  a generic representation has nonzero `ψ̄`-functionals (JPSS §2.1, printed
  page 385). This transport does not supply genericity for a representation
  without the original nonzero functional.
- **Equality and existence of factors.** Agreement of two factors is
  expressed as one common witness of both relations. Each relation has at most
  one solution (`IsPadicSymmetricGammaFactor.unique`,
  `IsPadicSymmetricEpsilonFactor.unique`,
  `IsPadicSymmetricLPolynomial.unique`), so a common witness is equality of
  the factors. The conclusions also assert that the factors exist: the
  nonvacuity parts of the relations (a compatible quotient measure, nonzero
  functionals for both representations and, for gamma and epsilon, a nonzero
  integral) and the functional equations of JPSS 1983 Theorem 2.7. Jacquet and
  Shalika take these from JPSS. Compatible quotient-measure existence is
  proved by `quotientHaarExistence` in `RankinSelberg/QuotientHaarExistence`,
  and inverse-character transport is available as above. The analytic
  existence inputs and the stability conclusions remain proof obligations;
  each conclusion claims factor existence together with the equality.
- **Measures.** As in Jacquet and Shalika (Section 2.1, display (4)), the
  additive measure is the self-dual one, `ν.val`. The statements do not assert
  that such a measure exists; that is the separate published
  `SelfDualMeasureExists`, and without it the statements hold vacuously. All
  compatible quotient measures are quantified. For the fixed
  `generalLinearHaar` and `unipotentHaar` normalizations,
  `unipotentQuotientHaar_unique` in `RankinSelberg/UnipotentQuotient` proves
  that each is exactly `unipotentQuotientHaar`; the same module proves
  existence by `unipotent_compatibleMeasureExists`. This uniqueness concerns
  those fixed Haar measures. Separately, a positive scalar does not change
  the L-polynomial (published `isPairLPolynomial_smul_measure`). The
  L-polynomial does not depend on `ν` or `ψ` either, which is not proved in the
  Library; the L-statement keeps the paper's standing assumption on `ψ`.
- **Epsilon statement.** Section 1.1 asserts the pair analogue of display (2)
  and announces its proof in Section 4. The ε-equality follows from
  Propositions 4.1 and 5.1: by 5.1, applied also to the contragredients
  `π̃_i ⊗ χ^{-1}` and `σ̃` (`χ^{-1}` has the same conductor), the L-factors in
  display (4.1)(1) are `1`, so `ε = γ` for both twists. The L-equality part of
  the analogue is the L-statement.
- **Field.** `F` is a p-adic field (a finite extension of `Q_p`), not an
  arbitrary nonarchimedean local field: the canonical topological data and the
  self-dual measures are published only for `PadicField`.
- **Universes.** The twisted representations live in universe `uV` and `σ` in
  `uW`. `Langlands.padicIrreducibleSmoothSmallRealization` in
  `Smooth/SmallRealizationProof` supplies an equivalent irreducible smooth
  complex representation in any independently prescribed carrier universe,
  for any `F.TopologicalData` and rank. Its proof chooses a countable basis
  inside the spanning orbit of a nonzero smooth vector and realizes the
  carrier as `Shrink.{uV} b →₀ ℂ`. It requires irreducibility and smoothness,
  with no additional admissibility assumption. The relations are invariant
  under equivalences between universes
  (`IsPadicSymmetricGammaFactor.congr_equiv`,
  `IsPadicSymmetricEpsilonFactor.congr_equiv`,
  `IsPadicSymmetricLPolynomial.congr_equiv`).
  So fixed carrier universes lose nothing for these representations.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `HighlyRamifiedStabilityStatement` was inspected: it returns
`Prop`, has universe parameters `uF uV uW`, and uses only `propext`,
`Classical.choice` and `Quot.sound`. There is no `sorry` and no new axiom.
