# Highly ramified stability of pair gamma factors in both factors

This module proves a two-factor form of the highly ramified stability of JPSS pair gamma
factors. The Library's stability theorem of Jacquet and Shalika
(`highlyRamifiedGammaStability`, statement `HighlyRamifiedGammaStabilityStatement`) changes
only the twisted first representation, keeps the second representation fixed, and assumes an
additive character of conductor exponent `0`. Here both representations may change, and the
additive character is arbitrary. The module is a supporting step for the stable pair gamma
comparison under highly ramified twists. It introduces no definition and no axiom.

The theorems `pairGammaStability_conductorZero` and `pairGammaStability` take the twist
exchange statement `PairGammaTwistExchangeStatement` (module
`Langlands.Representation.RankinSelberg.PairGammaTwistExchangeStatement`) as an explicit
hypothesis `hR1`; they prove nothing about that statement.

## Declarations

All declarations are in the namespace `Langlands.RankinSelberg.StableTwist`. Throughout, `F`
is a p-adic field with its canonical topological data, `π₁, π₂` are representations of
`GL_(r+1)(F)` on complex modules in one universe and `σ₁, σ₂` representations of
`GL_(t+1)(F)` on complex modules in another, all four `ψ`-generic (`Whittaker.IsGeneric`),
with `SameGLCentralCharacter F π₁ π₂` and `SameGLCentralCharacter F σ₁ σ₂`. "Twist by `χ`"
means `Langlands.twist (χ ∘ det)` applied to the first representation.

- `pairGammaStability_conductorZero hR1 F ψ ν hψ π₁ π₂ σ₁ σ₂ ...`: if `ψ` has additive
  conductor `0` and `ν` is a self-dual Haar measure for `ψ`, there is `A : ℕ` such that for
  every quasicharacter `χ` of `Fˣ` with multiplicative conductor at least `A`, any two
  symmetric p-adic gamma certificates (`IsPadicSymmetricGammaFactor F ψ ν`) `G` of
  `(π₁ ⊗ χ, σ₁)` and `G'` of `(π₂ ⊗ χ, σ₂)` are equal.
- `exists_conductorZero_scale F ψ`: every unitary additive character `ψ` is `ψ₀.scale b`
  (that is, `x ↦ ψ₀(b x)`) for some unitary additive character `ψ₀` of additive conductor `0`
  and some `b ∈ Fˣ`.
- `pairGammaStability hR1 F ψ ν π₁ π₂ σ₁ σ₂ ...`: the conclusion of
  `pairGammaStability_conductorZero` for an arbitrary unitary additive character `ψ` and a
  self-dual Haar measure `ν` for `ψ`.

## Implemented proofs

**Conductor zero.** Apply the Library's `highlyRamifiedGammaStability` twice:

1. to `(π₁, π₂; σ₁)`, giving `A₁` and, for `χ` of conductor at least `A₁`, a rational
   function `G₁` that is a certificate of both `(π₁ ⊗ χ, σ₁)` and `(π₂ ⊗ χ, σ₁)`;
2. to `(σ₁, σ₂; π₂)` (ranks exchanged), giving `A₂` and a `G₂` that is a certificate of both
   `(σ₁ ⊗ χ, π₂)` and `(σ₂ ⊗ χ, π₂)`.

Take `A = max A₁ A₂`. The symmetric relation is symmetric for representations of Whittaker
type (`Padic.isPadicSymmetricGammaFactor_comm`, with `isOfWhittakerType_of_isGeneric` and the
twisted genericity `isGeneric_quasicharacter_twist_iff`), so `G₂` is a certificate of
`(π₂, σ₁ ⊗ χ)` and of `(π₂, σ₂ ⊗ χ)`. The hypothesis `hR1` moves the twist to the first
factor: `G₂` is a certificate of `(π₂ ⊗ χ, σ₁)` and of `(π₂ ⊗ χ, σ₂)`. Uniqueness of
certificates (`IsPadicSymmetricGammaFactor.unique`) then gives
`G = G₁ = G₂ = G'`.

**Scaling to conductor zero.** With `ϖ` the uniformizer and `c` the additive conductor of
`ψ`, put `a = ϖ^(-c)`. Then `ψ.scale a` has conductor `c + ord(a) = 0`
(`additiveConductor_scale`), and `(ψ.scale a).scale a⁻¹ = ψ` (`scale_scale`, `scale_one`).

**Arbitrary character.** Write `ψ = ψ₀.scale b` with `ψ₀` of conductor `0`, and choose a
self-dual measure `ν₀` for `ψ₀` (`HighlyRamified.nonempty_selfDualHaar`). Genericity for `ψ`
and `ψ₀` agree (`isGeneric_iff_character`), so the conductor-zero theorem gives `A`. For `χ`
of conductor at least `A`, take the generic gamma certificates `G₀`, `G₀'` of
`(π₁ ⊗ χ, σ₁)` and `(π₂ ⊗ χ, σ₂)` at `(ψ₀, ν₀)` (`genericSymmetricGammaUnit_isPadic`). The
supporting module `GammaCharacterChange` (`genericGamma_characterChange`, with the central
characters `ω_π · χ^(r+1)` of the twists from `hasGLCentralCharacter_twist`) gives
`G = M · G₀` and `G' = M · G₀'` for the same monomial
`M = gammaCharacterChangeMonomial F r t (ω_π χ^(r+1)) ω_σ b`, because the two pairs have the
same ranks and central characters. Since `G₀ = G₀'` by the conductor-zero case, `G = G'`.

## Sources and provenance

The one-factor stability is Jacquet and Shalika, *A Lemma on Highly Ramified ε-Factors*,
Math. Ann. 271 (1985), Proposition (4.1), printed p.326
(`jacquet-shalika-1985-ramified-factors`), in the Library as `highlyRamifiedGammaStability`.
The two-factor form is the one used by Henniart, *On the local Langlands conjecture for GL(n):
the cyclic case*, Ann. of Math. 123 (1986), proof of Lemma 4.2, printed p.158
(`henniart-1986-cyclic`), who applies Jacquet–Shalika to each factor in turn. Moving the twist
from the second factor to the first, the passage from conductor `0` to an arbitrary additive
character, and the use of the symmetric relation are internal derivations from Library
results, described above.
