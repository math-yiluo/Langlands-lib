# Continuous additive characters of nonarchimedean groups and local fields

The module `Langlands.HarmonicAnalysis.AdditiveCharacterExists` proves that continuous complex
additive characters of nonarchimedean groups are locally constant, that nonarchimedean local fields
are nonarchimedean additive groups, and that every nonarchimedean local field, of any
characteristic, has a continuous non-trivial unitary additive character.

## Content

- `isLocallyConstant_of_continuous_addChar`: for a nonarchimedean topological additive group `A`
  (open subgroups form a basis at `0`) and a continuous `ψ : AddChar A ℂ`, `ψ` is locally
  constant. An open subgroup `V` on which `‖ψ - 1‖ < ½` exists; all powers of `ψ(v)`, `v ∈ V`,
  stay in that disc, so `ψ(v) = 1` (`ℂˣ` has no small subgroups:
  `Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt`); then `ψ` is constant on cosets of
  `V`. The multiplicative analogue is the Library's
  `Langlands.RankinSelberg.isLocallyConstant_of_continuous_complex_character`.
- `nonarchimedeanAddGroup_of_isNonarchimedeanLocalField` (instance): the balls
  `{x | v(x) < γ}`, `γ ≠ 0`, are additive subgroups and form a basis of neighbourhoods of `0`.
  Mathlib proves this for the topology defined from a valuative relation, not for a topology that
  is merely valuative (`IsValuativeTopology`), which is the case of `IsNonarchimedeanLocalField`.
- `UnitaryAdditiveCharacter.complex_ne_one`: the complex character of a
  `UnitaryAdditiveCharacter` is non-trivial.
- `nonempty_unitaryAdditiveCharacter F`: a `Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter F`
  exists. Take `r` with `0 < v(r) < 1`; the class of `r⁻¹` in `F / 𝒪` is not zero, so a character
  `χ : F / 𝒪 → ℚ / ℤ` does not vanish on it (`ℚ / ℤ` is an injective cogenerator:
  `CharacterModule.exists_character_apply_ne_zero_of_ne_zero`); then
  `ψ(t) = exp(2πi χ(t mod 𝒪))`, through `ℚ / ℤ → ℝ / ℤ → Circle`, is continuous because `𝒪` is open
  and `F / 𝒪` discrete, and `ψ(r⁻¹) ≠ 1` because `ℚ / ℤ → ℝ / ℤ` and `AddCircle.toCircle` are
  injective.
- `exists_addChar_continuous_ne_one F`: the same with values in `ℂ`.

The Library's `padicUnitaryAdditiveCharacterExists`
(`Langlands/HarmonicAnalysis/PadicUnitaryAdditiveCharacterExistsProof.lean`) is the same existence
for the Library's `PadicField` structures; the theorem here is for Mathlib's class
`IsNonarchimedeanLocalField`, in every characteristic.

## Source and licence

`nonempty_unitaryAdditiveCharacter` is lines 684–715 (`SvN.exists_char`) of
`src/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`
of <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`. The repository
has no licence file; the text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `GlobalTheory.Published.SvN.exists_char F : ∃ ψ : AddChar F ℂ, Continuous ψ ∧ ψ ≠ 1` →
  `Langlands.HarmonicAnalysis.nonempty_unitaryAdditiveCharacter F`, with values in `Circle` (the
  Library's `UnitaryAdditiveCharacter`); the source's form is the corollary
  `exists_addChar_continuous_ne_one`. The character is built directly as an `AddChar F Circle`
  (the source went through `F / 𝒪 →+ Additive ℂˣ`).
- The openness of `𝒪` is proved inline (the source's `int_mem_nhds`).
- New: `isLocallyConstant_of_continuous_addChar`, the instance
  `nonarchimedeanAddGroup_of_isNonarchimedeanLocalField`, `UnitaryAdditiveCharacter.complex_ne_one`.
- Universe of `F` arbitrary (the source: `Type`).

## Declarations

- `isLocallyConstant_of_continuous_addChar`
- `instance nonarchimedeanAddGroup_of_isNonarchimedeanLocalField`
- `UnitaryAdditiveCharacter.complex_ne_one`
- `nonempty_unitaryAdditiveCharacter`, `exists_addChar_continuous_ne_one`

## Dependencies

`Langlands.HarmonicAnalysis.Basic` (`UnitaryAdditiveCharacter`),
`Langlands.Representation.Twist.ContinuousCharacterProof`
(`complex_eq_one_of_forall_norm_pow_sub_one_lt`); Mathlib: `Algebra.Module.CharacterModule`,
`Analysis.SpecialFunctions.Complex.Circle`, `NumberTheory.LocalField.Basic`,
`Topology.Algebra.Nonarchimedean.Basic`.
