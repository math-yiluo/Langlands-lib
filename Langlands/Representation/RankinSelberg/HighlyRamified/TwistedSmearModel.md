# The twisted smeared second dual is a model function

Module `Langlands.Representation.RankinSelberg.HighlyRamified.TwistedSmearModel`.

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`
(Jacquet–Shalika 1985, §4.4, printed pages 329–330). Jacquet and Shalika apply the
functional equation of the pair `(σ ⊗ χ, τ)` to their vector `W'` (printed page 329). This
project instead applies the published functional equation to the pair `(σ̃ ⊗ χ⁻¹, τ)`, an
internal choice. Its `GL_(m+2)` vector is the `χ⁻¹`-twisted smeared
second dual function `g ↦ χ(det g)⁻¹ ∫ S(x) f̃'(g ū_x) dx`
(`HighlyRamified.DualShell.twistedSmear` with `S = dualWeightFourier …`). This module
proves that this function lies in a Whittaker model of the twisted inverse transpose,
for a nonzero functional for the standard character of `ψ`, and that it is right
invariant under an open subgroup. It also proves that the twisted inverse transpose
is `ψ`-generic. The canonical topology, valuation and Borel structure of the p-adic
field are local instances.

## Provenance

Jacquet and Shalika need no analogue of these facts in this form. The formal statements
and proofs are internal to this project. They are assembled from the published
`DualModels` (second dual functionals and functions), `HighlyRamified.Duality`
(genericity of the inverse transpose), `HighlyRamified.DualSmear` (smearing along
lower rows) and the determinant-twist genericity lemma in `HighlyRamifiedGammaAssembly`.

## Declarations

Let `σ` be a representation of `GL_(m+2)` on `W`, and write `σ^ι` for
`inverseTransposePullback σ`, the pullback of `σ` along `g ↦ ᵗg⁻¹`.

- `inverseTransposeFunctional F ψ σ ℓ`: for a functional `ℓ` of `σ` for the inverse
  standard character of `ψ`, the second dual functional
  `secondDualFunctional ψ σ ℓ` of `σ^ι`. It is stated for the inverse standard
  character of `ψ.scale (-1)`, and here it is read as a functional for the standard
  character of `ψ`. The two characters are equal by
  `inverseStandardCharacter_scale_neg_one`. The underlying linear form is unchanged.
- `isGeneric_inverseTransposePullback_of_inverse F ψ σ hσ ℓ hℓ`: if `σ` is `ψ`-generic
  and has a nonzero functional `ℓ` for the inverse character, then `σ^ι` is
  `ψ`-generic. Irreducibility and admissibility of `σ^ι` come from
  `isGeneric_inverseTransposePullback`. The nonzero `ψ`-functional is
  `inverseTransposeFunctional F ψ σ ℓ`, which is nonzero by
  `secondDualFunctional_ne_zero`.
- `inverseQuasicharacter F χ hχ`: a continuous character `χ : Fˣ →* ℂˣ`, inverted, as a
  `Quasicharacter`.
- `isGeneric_twist_inverseTransposePullback F ψ σ hσ ℓ' hℓ' χ hχ`: for continuous `χ`,
  the twist `twist (χ⁻¹ ∘ det) σ^ι` is `ψ`-generic. Apply
  `isGeneric_quasicharacter_twist` to the previous lemma.
- `rectangularMeasure_isFiniteMeasureOnCompacts F η j t`: the product Haar measure
  `rectangularMeasure η j t` on `j × t` matrices is finite on compact sets. It is a
  finite product of copies of the additive Haar measure `η`.
- `exists_twistedSmear_model F ψ η σ hσ ℓ' hℓ' f' χ hχ S hS hSc`: let `σ` be
  `ψ`-generic, `ℓ'` a nonzero functional of `σ` for the inverse character,
  `f' ∈ coefficientModel σ ℓ'`, `χ` continuous, and
  `S : Matrix (Fin 1) (Fin (m+1)) F → ℂ` locally constant with compact support. Then
  there are
  - a functional `ℓF` of `twist (χ⁻¹ ∘ det) σ^ι` for the standard character of `ψ`,
    with `ℓF ≠ 0`;
  - a function `Fbig` of `coefficientModel (twist (χ⁻¹ ∘ det) σ^ι) ℓF` with
    `Fbig(g) = χ(det g)⁻¹ ∫ S(x) f̃'(g ū_x) dx` for every `g`, where
    `f̃' = secondDualFunction ψ (m+1) f'`, `ū_x = lowerRow x`, and the integral is over
    `rectangularMeasure η 1 (m+1)`;
  - an open subgroup `L` of `GL_(m+2)` with `Fbig(g l) = Fbig(g)` for all `g` and all
    `l ∈ L`.

## Proof of `exists_twistedSmear_model`

Write `ℓ̃ = secondDualFunctional ψ σ ℓ'`.

1. `ℓF` is `twistFunctional` (with `determinantCharacter_unipotent`) applied to
   `inverseTransposeFunctional F ψ σ ℓ'`. The twist keeps the linear form `ℓ̃`, so
   `ℓF ≠ 0` by `secondDualFunctional_ne_zero`.
2. Choose `v` with `f' = coefficientMap σ ℓ' v`. By
   `secondDualFunction_coefficient`, `f̃'(h) = ℓ̃(σ^ι(h) v)` for every `h`.
3. `σ^ι` is smooth, by `isGeneric_inverseTransposePullback`. Let
   `w = lowerRowSmear (rectangularMeasure η 1 (m+1)) σ^ι … S hS hSc v`, the vector
   `∫ S(x) σ^ι(ū_x) v dx`, and let `Fbig` be the coefficient of the twisted
   representation at `w` for `ℓF`. By the definition of the twist,
   `Fbig(g) = ℓ̃(χ⁻¹(det g) · σ^ι(g) w)`.
4. Linearity of `ℓ̃` gives the factor `χ(det g)⁻¹`. `lowerRowSmear_dual`, applied to
   the linear form `ℓ̃ ∘ σ^ι(g)`, gives
   `ℓ̃(σ^ι(g) w) = ∫ S(x) ℓ̃(σ^ι(g ū_x) v) dx`. By step 2 this equals
   `∫ S(x) f̃'(g ū_x) dx`.
5. The twisted representation is smooth, by
   `isGeneric_twist_inverseTransposePullback`. Let `L` be an open subgroup fixing `w`.
   Then for `l ∈ L`, `Fbig(g l) = ℓF(ρ(g) ρ(l) w) = ℓF(ρ(g) w) = Fbig(g)`, where `ρ` is
   the twisted representation.
