# Surjectivity of the stable images from surjectivity of the extension

Author: Worker 4803. Module `Langlands.Correspondence.HenniartSurjectivityTransfer`,
namespace `Langlands.Henniart.Extension`. A supporting module of
`HenniartSurjectivityStepProof`; it defines no statement.

## Content

- `supercuspidalCentralActsBy_unique`: the scalar by which a central element `a`
  acts on a supercuspidal class is unique; an irreducible representation has a nonzero
  vector (`AssemblyDeterminant.exists_ne_zero_of_isIrreducible`).
- `exists_pow_eq_one_of_stableTwist`: let `π₀` be the stable image of a unitary class
  `b₀` factoring through a finite quotient `Q`, and `π = z · π₀` a unitary class with
  central character `ω` of finite order. Then `z` is a root of unity. A candidate for
  `b₀` gives a central character `ω₀` of `π₀` with `ω₀ ∘ rec = det b₀`
  (`DeterminantCompatibility`); at a preimage of the uniformizer `ϖ` under reciprocity,
  `ω₀(ϖ)^|Q| = 1` (`determinant_pow_card_eq_one`). Twisting by `χ ∘ det`, where `χ`
  is the unramified character of `Kˣ` with `χ(ϖ) = z`, multiplies the central
  character at `ϖ` by `z^n` (`supercuspidalCentralActsBy_twist`), so
  `ω(ϖ) = z^n ω₀(ϖ)` and `z^(n N₁ |Q|) = 1` for `ω^(N₁) = 1`.
- `stableSurjectiveAt_of_surjective`: let `hS : StableExistsAt K n`, assume candidate
  existence, a geometric reciprocity candidate, and that `rankExtension K hS` is
  surjective. Then `StableSurjectiveAt K n`. For `π` unitary of rank `n` with central
  character of finite order, surjectivity gives `σ` with stable decomposition
  `σ = z · b₀` and `π = z · π₀`. By the previous lemma `z` is a root of unity, and
  `‖z‖ = 1`. The twist `b₁ = z · b₀` is unitary and factors through a finite quotient
  (`isFiniteFactoring_twist`), so it has a stable image `y` (`hS`). A candidate for
  `b₀` and `b₁` (`exists_common_candidate₂`) sends `b₁` to `z · π₀ = π`
  (`candidate_twist_generator`) and to `y`, so `y` is the generator of `π`.

## Provenance

Internal. Henniart (2000), §4.3, last sentence, printed p. 453 (PDF p. 15): the
surjectivity of the stable images comes from Henniart (1988). The identification of
an unramified twist of a stable image as a stable image uses the candidates' twist
compatibility (Henniart 2000, §3.8).
