# Unitary characters of `A_G`

Module `Langlands.Global.AdelicSplitCentreUnitaryCharacter`, namespace
`Langlands.Global.RestrictionSplitCentre`.

`F : Type` is a number field and `G` a group scheme over `Spec F`, affine, affine over the base
and locally of finite type. `A_G` is `canonicalSubgroup F G` (module
`Langlands.Global.AdelicRestrictionSplitCentreCanonical`), the positive real points of the chosen
split component of `Res_{F/ℚ} G`, equal to `imageSubgroup F T₀ G i₀` for the chosen split component
`i₀ = canonicalComponent F G` of `G` (`canonicalSubgroup_eq_imageSubgroup`).

## Declarations

- `canonicalSubgroup_le_center`: `A_G ≤ Subgroup.center (AdelicGroupPoints F G)`. The split
  component is central (`IsSplitComponent.isCentralSplitTorus.isCentral`), so the points of its
  image commute with all points (`commute_of_mem_center`).
- `exists_realParameter_of_unitary`: for connected reductive `G`, let `c : G(𝔸) → ℂ` be continuous,
  with `c (a b) = c a * c b` and `‖c a‖ = 1` for `a, b ∈ A_G`. Then there is
  `ν : RealCharacterParameter F G` (that is, `ν ∈ X^*(G) ⊗ ℝ`) with
  `c a = parameterPower F G (imaginaryParameter F G ν) a` for every `a ∈ A_G`; in the notation of
  the sources, `c(a) = a^{iν}`.

## Proof of `exists_realParameter_of_unitary`

Let `s = PositiveRealTorus.logSection` for the chosen split component, with the injectivity
`canonical_characterRestrict_injective` (from `centralSplitTorusCharacter`), the finite index
`canonical_finiteIndex` and a splitting of the torus. It is a continuous homomorphism
`Hom(X^*(G), ℝ) → G(𝔸)` whose range is `A_G` (`logSection_range`) and which is a section of
`characterLog = H_G` (`characterLogHom_logSection`); hence `a = s (H_G a)` for `a ∈ A_G`. Then
`ψ = c ∘ s` is a continuous homomorphism from `RealCharacterDual F G = Hom(X^*(G), ℝ)` to the
complex numbers of modulus one. `X^*(G)` is free of finite rank (`rationalCharacterLattice`); take a
`ℤ`-basis `χᵢ` and the dual functionals `eᵢ`. Every `H` is `∑ᵢ H(χᵢ) eᵢ`. Each
`t ↦ ψ(t eᵢ)` is a continuous character of `ℝ`, hence `t ↦ exp(zᵢ t)`
(`ContinuousCharacterReal.exists_eq_exp`), and `|ψ| = 1` forces `Re zᵢ = 0`; write `zᵢ = i aᵢ`.
Then `ψ(H) = exp(i ∑ᵢ aᵢ H(χᵢ))`. With `ν = ∑ᵢ aᵢ ⊗ χᵢ`,
`complexParameterPairing F G (imaginaryParameter F G ν) H = ∑ᵢ i aᵢ H(χᵢ)`, so
`c a = ψ(H_G a) = exp ⟨iν, H_G(a)⟩ = parameterPower F G (imaginaryParameter F G ν) a`.

## Provenance

The fact that a unitary character of `A_G`, a vector group identified with `Hom(X^*(G), ℝ)` by
`H_G`, is `a ↦ a^{iν}`, as used after the proof of Delorme, *On the spectral theorem of Langlands*,
Adv. Math. 426 (2023), Lemma 7.10; the parameters follow Bernstein–Lapid §2.1 and
Mœglin–Waldspurger I.1.4, as in `Langlands.Global.AdelicComplexParameters`.
