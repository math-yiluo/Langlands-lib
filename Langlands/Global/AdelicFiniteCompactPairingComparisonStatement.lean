import Langlands.Global.AdelicTemperedVanishingReduction

/-! # Finite changes of the Iwasawa compact in `A^2_P` and in the Levi pairings (3.7)

For a standard parabolic `P = P_J` of a compatible family and two maximal compact subgroups
`K₁`, `K₂` of `G(𝔸)` with `P(𝔸) K_i = G(𝔸)` and the same infinite projection, the difference
`Δ = H_P^{K₁} - H_P^{K₂}` of the Iwasawa heights takes finitely many values on clopen fibres.
Cutting `φ` along the fibre `Δ = v` carries Lapid's `A^2_P` for `K₁` into `A^2_P` for `K₂`, and
the pairing of Delorme 2023, (3.7), for `K₁` at a point `x` of `𝔄_P` becomes, after the factors
`δ_P(x)⁻¹` and `δ_P(x')⁻¹`, a fixed positive multiple of the pairing for `K₂` at the point `x'`
with `H_P(x') = H_P(x) - v` (Mœglin–Waldspurger I.1.13). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The change of finite Iwasawa compact in `A^2_P` and in the pairings of Delorme 2023, (3.7).
Let `P = P_J` be a standard parabolic of a compatible family `𝓕` and `K₁`, `K₂` maximal compact
subgroups of `G(𝔸)` with `P(𝔸) K_i = G(𝔸)` and the same image in `G(𝔸_∞)`. Put
`Δ = H_P^{K₁} - H_P^{K₂}` and `φ_v = 1_{Δ = v} φ`. Then

* `Δ` takes finitely many values, and each fibre `{Δ = v}` is clopen;
* for every `φ ∈ A^2_P` for `K₁` (with `rho`, `hsmooth`, `hcalc`) and every `v`, `φ_v` lies in
  `A^2_P` for `K₂` with the same `rho`, `hsmooth`, `hcalc`;
* there is a constant `c > 0` such that for all continuous left `U(𝔸) M(F)`-invariant `φ`, `ψ`,
  every `v` and all `x, x' ∈ 𝔄_P` with `H_P(x') = H_P(x) - v`, the pairing integrand of
  `(φ_v, ψ)` on `K₁ × M(F) \ M(𝔸)^1` at `x` is integrable if and only if the one on
  `K₂ × M(F) \ M(𝔸)^1` at `x'` is, and
  `δ_P(x)⁻¹ ∫_{K₁ × M(F) \ M(𝔸)^1} = c · δ_P(x')⁻¹ ∫_{K₂ × M(F) \ M(𝔸)^1}`. -/
def FiniteCompactPairingComparisonStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)
    [IsClosedImmersion (𝓕.p J).hom.hom.left]
    (K₁ K₂ : Subgroup (AdelicGroupPoints F G))
    (hK₁ : IsIwasawaCompact (𝓕.p J) K₁) (hK₂ : IsIwasawaCompact (𝓕.p J) K₂),
    IsMaximalCompactSubgroup F G K₁ → IsMaximalCompactSubgroup F G K₂ →
    K₁.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom →
    let Δ : AdelicGroupPoints F G → RealCharacterDual F (𝓕.P J) :=
      fun g => hK₁.height g - hK₂.height g
    let cut : RealCharacterDual F (𝓕.P J) → (AdelicGroupPoints F G → ℂ) →
        AdelicGroupPoints F G → ℂ :=
      fun v φ => {g | Δ g = v}.indicator φ
    let Γ : Subgroup (AdelicGroupPoints F G) :=
      parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J)
    let δinv : AdelicGroupPoints F (𝓕.P J) → ℂ :=
      parameterPower F (𝓕.P J) (-modulusParameter F (𝓕.P J))
    (∃ S : Finset (RealCharacterDual F (𝓕.P J)), ∀ g, Δ g ∈ S) ∧
    (∀ v : RealCharacterDual F (𝓕.P J), IsClopen {g | Δ g = v}) ∧
    (∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsSquareIntegrableInducedForm K₁ hK₁.isCompact rho hsmooth hcalc (𝓕.p J) (𝓕.iU J)
        (𝓕.l J) φ →
      ∀ v : RealCharacterDual F (𝓕.P J),
        IsSquareIntegrableInducedForm K₂ hK₂.isCompact rho hsmooth hcalc (𝓕.p J) (𝓕.iU J)
          (𝓕.l J) (cut v φ)) ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ φ ψ : AdelicGroupPoints F G → ℂ,
        Continuous φ → IsLeftInvariantUnder F G Γ φ →
        Continuous ψ → IsLeftInvariantUnder F G Γ ψ →
        ∀ (v : RealCharacterDual F (𝓕.P J)) (x x' : AdelicGroupPoints F (𝓕.P J)),
          x ∈ 𝓕.positiveSplitComponent J → x' ∈ 𝓕.positiveSplitComponent J →
          characterLog F (𝓕.P J) x' = characterLog F (𝓕.P J) x - v →
          (Integrable (𝓕.squareIntegrablePairingIntegrand K₁ J x (cut v φ) ψ)
              (𝓕.squareIntegrablePairingMeasure K₁ hK₁.isCompact J) ↔
            Integrable (𝓕.squareIntegrablePairingIntegrand K₂ J x' (cut v φ) ψ)
              (𝓕.squareIntegrablePairingMeasure K₂ hK₂.isCompact J)) ∧
          δinv x * ∫ z, 𝓕.squareIntegrablePairingIntegrand K₁ J x (cut v φ) ψ z
              ∂(𝓕.squareIntegrablePairingMeasure K₁ hK₁.isCompact J) =
            (c : ℂ) * (δinv x' * ∫ z, 𝓕.squareIntegrablePairingIntegrand K₂ J x' (cut v φ) ψ z
              ∂(𝓕.squareIntegrablePairingMeasure K₂ hK₂.isCompact J))

end Langlands.Global
