import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralFourierInversion
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionVanishing
import Langlands.Representation.Plancherel.UnramifiedCharacters

/-! # The family `(p_χ φ)_{χ ∈ Â_G}` and the end of the proof of Theorem VIII.1.1

Waldspurger 2003, VIII.5 (printed p. 332): for `φ ∈ °C(G)` with `ω(ˇφ) = 0` for every
`ω ∈ E₂(G)`, Fourier inversion on `A_G` gives `χ ∈ Â_G` with `p_χ φ ≠ 0` when `φ ≠ 0`, and
Theorem VIII.4.2 then yields a contradiction. This module indexes the projections `p_χ` by the
Library's `unitaryCharacters A` (the continuous unitary characters of `A`, Waldspurger's `Â_G`
for `A = A_G`), states Fourier inversion as injectivity of `φ ↦ (p_χ φ)_χ` on `C(G)`, and
combines it with `centralProjection_eq_zero_of_schwartzAction_eq_zero`.
-/

noncomputable section

open MeasureTheory
open Langlands.Plancherel (unitaryCharacters)
open Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

universe u v

section Family

variable {G : Type u} [Group G] [TopologicalSpace G] {A : Subgroup G}

/-- A unitary character `χ : A →* ℂˣ` whose values `a ↦ χ(a) ∈ ℂ` depend continuously on `a`,
as an element of `unitaryCharacters A`. -/
def unitaryCharacterOfContinuous (χ : A →* ℂˣ) (h1 : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (hc : Continuous fun a => (χ a : ℂ)) : unitaryCharacters A :=
  ⟨⟨χ, Units.continuous_iff.mpr ⟨hc, by
    simp_rw [Units.val_inv_eq_inv_val]
    exact hc.inv₀ fun a => (χ a).ne_zero⟩⟩, h1⟩

@[simp] theorem unitaryCharacterOfContinuous_apply (χ : A →* ℂˣ) (h1 : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (hc : Continuous fun a => (χ a : ℂ)) (a : A) :
    (unitaryCharacterOfContinuous χ h1 hc : A →ₜ* ℂˣ) a = χ a :=
  rfl

variable [MeasurableSpace A] [OpensMeasurableSpace A]

/-- An element of `unitaryCharacters A` is a unitary measurable character. -/
theorem isUnitaryCharacter_of_mem_unitaryCharacters (χ : unitaryCharacters A) :
    IsUnitaryCharacter (χ : A →ₜ* ℂˣ).toMonoidHom where
  norm_eq_one a := χ.2 a
  measurable := (Units.continuous_val.comp (χ : A →ₜ* ℂˣ).continuous).measurable

variable [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)] {μA : Measure A}
  {Ξ σ : G → ℝ}

/-- Waldspurger's family `(p_χ f)_{χ ∈ Â_G}` (VIII.4, VIII.5) as a linear map on `C(G)`:
`f ↦ (χ ↦ p_χ f)`, indexed by the continuous unitary characters of `A`. -/
def Space.centralProjectionFamily (hw : CentralWeights μA Ξ σ) :
    Space Ξ σ →ₗ[ℂ] (unitaryCharacters A → G → ℂ) :=
  LinearMap.pi fun χ => Space.centralProjection hw (isUnitaryCharacter_of_mem_unitaryCharacters χ)

@[simp] theorem Space.centralProjectionFamily_apply (hw : CentralWeights μA Ξ σ)
    (f : Space Ξ σ) (χ : unitaryCharacters A) :
    Space.centralProjectionFamily hw f χ =
      HarishChandraSchwartz.centralProjection μA (χ : A →ₜ* ℂˣ).toMonoidHom f :=
  rfl

/-- **Fourier inversion on `A_G`** (Waldspurger, VIII.5) over `Â_G = unitaryCharacters A`: for
`A` closed, central and with `A / (A ∩ K)` finitely generated for every compact open `K`,
`f ↦ (p_χ f)_{χ ∈ Â_G}` is injective on `C(G)`. -/
theorem Space.centralProjectionFamily_injective [MeasurableMul A] [μA.IsMulLeftInvariant]
    [μA.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μA] (hw : CentralWeights μA Ξ σ)
    (hA : IsClosed (A : Set G)) (hAc : A ≤ Subgroup.center G)
    (hFG : HasFGCompactOpenQuotients A) :
    Function.Injective (Space.centralProjectionFamily hw) := by
  refine (injective_iff_map_eq_zero (Space.centralProjectionFamily hw)).mpr fun f hf => ?_
  have h := eq_zero_of_forall_centralProjection_eq_zero hw hA hAc hFG (Space.coe_mem f)
    fun χ h1 hc => congrFun hf (unitaryCharacterOfContinuous χ h1 hc)
  exact Space.ext fun g => congrFun h g

end Family

section EndOfProof

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {A : Subgroup G} [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]

/-- **End of the proof of Theorem VIII.1.1** (Waldspurger, VIII.5), abstract form: let `A` be a
closed central subgroup with `A / (A ∩ K)` finitely generated for every compact open `K`, and
`φ ∈ C(G)`. Suppose that for every `χ ∈ Â_G = unitaryCharacters A` there are a smooth
representation `ρ_χ` with an invariant positive form and a class `p_χ` of subrepresentations
`S`, each admissible with tempered coefficients and with `π_S(ˇφ) = 0`, such that
`p_χ φ ∈ Σ_S A(S)` (for Waldspurger, Theorem VIII.4.2 with `p_χ` the `ω ∈ E₂(G)_χ`). Then
`φ = 0`. -/
theorem Space.eq_zero_of_forall_schwartzAction_eq_zero [MeasurableMul A] {μA : Measure A}
    [μA.IsHaarMeasure] [μA.IsMulRightInvariant] [SFinite μA] {μG : Measure G}
    [IsFiniteMeasureOnCompacts μG]
    [μG.IsMulLeftInvariant] [μG.IsInvInvariant] {ν : Measure (LeftQuotient A)}
    (hA : IsClosed (A : Set G)) (hAc : A ≤ Subgroup.center G)
    (hFG : HasFGCompactOpenQuotients A) (hν : IsCompatible A μG μA ν) {Ξ σ : G → ℝ}
    (hwA : CentralWeights μA Ξ σ) (hw : L2Weights μG Ξ σ) (hΞ : ∀ g, Ξ g⁻¹ = Ξ g)
    (hσ : ∀ g, σ g⁻¹ = σ g) {V : unitaryCharacters A → Type v} [∀ χ, AddCommGroup (V χ)]
    [∀ χ, Module ℂ (V χ)] {ρ : ∀ χ, Representation ℂ G (V χ)}
    (b : ∀ χ, InvariantPositiveForm (ρ χ)) (hs : ∀ χ, IsSmooth (ρ χ))
    {p : ∀ χ, Subrepresentation (ρ χ) → Prop} (φ : Space Ξ σ)
    (hS : ∀ χ S, p χ S → ∃ (hSa : IsAdmissible S.toRepresentation)
      (hT : HasTemperedCoefficients Ξ σ S.toRepresentation),
      schwartzAction hw hSa hT (Space.check hΞ hσ φ) = 0)
    (hmem : ∀ χ, ∃ c ∈ subrepresentationCoefficientSpace (hs χ) (p χ),
      ⇑c = HarishChandraSchwartz.centralProjection μA (χ : A →ₜ* ℂˣ).toMonoidHom φ) :
    φ = 0 := by
  refine Space.centralProjectionFamily_injective hwA hA hAc hFG ?_
  rw [map_zero]
  funext χ
  exact centralProjection_eq_zero_of_schwartzAction_eq_zero hA hAc hν
    (isUnitaryCharacter_of_mem_unitaryCharacters χ) hw hΞ hσ (b χ) (hs χ) φ (hS χ) (hmem χ)

end EndOfProof

end Langlands.HarishChandraSchwartz
