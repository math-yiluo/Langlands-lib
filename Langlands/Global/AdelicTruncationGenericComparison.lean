import Langlands.Global.AdelicEisensteinTemperedTruncationEstimate
import Langlands.Global.AdelicTruncationAffineDenominators

/-! # The characteristic comparison from generic spectral estimates -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Metric
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Global.AdelicGroupPoints Langlands.Global.AdelicSiegelFactors
  Langlands.Global.ImaginaryAxis

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- From the generic spectral estimate and a permissible local pole presentation, the
actual characteristic and regularized pairings satisfy the holomorphic extension and
all-imaginary estimate clauses of the truncation comparison. -/
def GenericTruncationComparisonStatement : Prop :=
  ∀ {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅))
    (T₀ : V fam.T) (vol : StandardIndex F G fam.i fam.ν → ℝ)
    (P : StandardIndex F G fam.i fam.ν) (Φ : AdelicGroupPoints F G → ℂ)
    (E : ComplexCharacterParameter F (fam.P P) → AdelicGroupPoints F G → ℂ)
    {n nT nZ : ℕ} (ec : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F (fam.P P))
    (eT : V fam.T ≃ₗ[ℝ] (Fin nT → ℝ))
    (eZ : RealCharacterDual F (fam.P fam.top) ≃ₗ[ℝ] (Fin nZ → ℝ))
    (R : ℝ) (L : ∀ Q, fam.AffineExponentLabels P Q)
    (expansion : (Fin n → ℝ) → fam.positiveSplitComponent fam.top →
      ∀ Q, fam.UnitaryPairingExpansion Q)
    (f : V fam.T → fam.positiveSplitComponent fam.top → (Fin n → ℂ) → ℂ),
  let D := ec ⁻¹' fam.genericParameterRegion P L
  let A (T : V fam.T) (z : fam.positiveSplitComponent fam.top) (x : Fin n → ℝ) :=
    fam.truncatedPairing hK C T₀ T z (E (ec (imaginarySlice x))) Φ
  let weight (ε : ℝ) (k : ℕ) (T : V fam.T) (z : fam.positiveSplitComponent fam.top) :=
    Real.exp (-ε * ‖eT T‖) * (1 + ‖eZ (characterLog F (fam.P fam.top) z.val)‖ ^ k)
  let regular := fam.IsRegularTruncationParameter R
  let sector (δ : ℝ) (T : V fam.T) :=
    ∀ α ∈ simpleRelativeRoots fam.i fam.ν, δ * ‖eT T‖ ≤ eval fam.T α T
  0 < R →
  (∀ Q (k : Fin (L Q).size) (α : fam.relativeSimpleRoots Q), ∃ x : Fin n → ℝ,
    fam.corootValue Q ((L Q).label k (ec (imaginarySlice x))) α ≠ 0) →
  (∀ T, regular T → ∀ z, Continuous (A T z) ∧
    ∀ x, IntegrableOn (fam.truncatedPairingIntegrand z (E (ec (imaginarySlice x))) Φ)
      (fam.truncationRegion hK C T₀ T) (normOneRationalQuotientHaarMeasure F G)) →
  (∀ T, regular T → ∀ z, DifferentiableOn ℂ (f T z) D ∧
    HasImaginaryHyperplanePresentation (f T z) D ∧
    ∀ x ∈ imaginarySlice ⁻¹' D,
      f T z (imaginarySlice x) = fam.regularizedPairing vol (expansion x z) T) →
  (∀ δ : ℝ, 0 < δ → ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
    ∃ (B ε : ℝ) (k : ℕ), 0 < B ∧ 0 < ε ∧
    ∀ T, regular T → sector δ T → ∀ z, ∀ x ∈ Λ ∩ imaginarySlice ⁻¹' D,
      ‖A T z x - f T z (imaginarySlice x)‖ ≤ B * weight ε k T z) →
  ∃ (ω : V fam.T → fam.positiveSplitComponent fam.top → (Fin n → ℂ) → ℂ)
    (Dω : V fam.T → fam.positiveSplitComponent fam.top → Set (Fin n → ℂ)),
    IsOpen (imaginarySlice ⁻¹' D) ∧ Dense (imaginarySlice ⁻¹' D) ∧
    (∀ T, regular T → ∀ z,
      IsOpen (Dω T z) ∧ Set.range (imaginarySlice (n := n)) ⊆ Dω T z ∧
      DifferentiableOn ℂ (ω T z) (Dω T z) ∧
      ∀ x ∈ imaginarySlice ⁻¹' D,
        ω T z (imaginarySlice x) = fam.regularizedPairing vol (expansion x z) T) ∧
    ∀ δ : ℝ, 0 < δ → ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
      ∃ (B ε : ℝ) (k : ℕ), 0 < B ∧ 0 < ε ∧
      ∀ T, regular T → sector δ T → ∀ z, ∀ x ∈ Λ,
        IntegrableOn (fam.truncatedPairingIntegrand z (E (ec (imaginarySlice x))) Φ)
          (fam.truncationRegion hK C T₀ T) (normOneRationalQuotientHaarMeasure F G) ∧
        ‖A T z x - ω T z (imaginarySlice x)‖ ≤ B * weight ε k T z

/-- Put each fixed regular truncation parameter in a strictly dominant sector, use the
generic bound for local division, then recover the same estimate by continuity on a ball
containing the prescribed bounded spectral set. -/
theorem genericTruncationComparison : fam.GenericTruncationComparisonStatement := by
  classical
  intro K hK C T₀ vol P Φ E n nT nZ ec eT eZ R L expansion f D A weight regular sector
    hR hne hA hf hbound
  obtain ⟨hD, hDc, hIo, hIc⟩ := fam.open_dense_genericParameterRegion P L ec hne
  have hsector (T : V fam.T) (hT : regular T) :
      ∃ δ : ℝ, 0 < δ ∧ sector δ T := by
    let a := ‖eT T‖ + 1
    have ha : 0 < a := by dsimp only [a]; positivity
    let δ := R / a
    have hδ : 0 < δ := div_pos hR ha
    refine ⟨δ, hδ, fun α hα => le_trans ?_ (hT.2 α hα)⟩
    calc δ * ‖eT T‖ ≤ δ * a :=
          mul_le_mul_of_nonneg_left (by dsimp only [a]; linarith) hδ.le
      _ = R := div_mul_cancel₀ _ ha.ne'
  have hext : ∀ (T : V fam.T) (z : fam.positiveSplitComponent fam.top),
      ∃ (ω : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)), regular T →
        IsOpen U ∧ Set.range (imaginarySlice (n := n)) ⊆ U ∧
          DifferentiableOn ℂ ω U ∧ EqOn ω (f T z) (U ∩ D) := by
    intro T z
    by_cases hT : regular T
    · obtain ⟨δ, hδ, hs⟩ := hsector T hT
      have hb (Λ : Set (Fin n → ℝ)) (hΛ : Bornology.IsBounded Λ) :
          ∃ B : ℝ, ∀ x ∈ Λ ∩ imaginarySlice ⁻¹' D,
            ‖A T z x - f T z (imaginarySlice x)‖ ≤ B := by
        obtain ⟨B, ε, k, _, _, h⟩ := hbound δ hδ Λ hΛ
        exact ⟨B * weight ε k T z, h T hT hs z⟩
      obtain ⟨ω, U, hU⟩ := exists_holomorphic_extension_of_generic_comparison hD hDc
        (hf T hT z).1 hIc (hf T hT z).2.1 (hA T hT z).1 hb
      exact ⟨ω, U, fun _ => hU⟩
    · exact ⟨fun _ => 0, ∅, fun h => (hT h).elim⟩
  choose ω U hω using hext
  refine ⟨ω, U, hIo, hIc, ?_, ?_⟩
  · intro T hT z
    obtain ⟨hU, hr, hhol, heq⟩ := hω T z hT
    refine ⟨hU, hr, hhol, fun x hx => ?_⟩
    exact (heq ⟨hr (mem_range_self x), hx⟩).trans ((hf T hT z).2.2 x hx)
  · intro δ hδ Λ hΛ
    obtain ⟨r, hr⟩ := hΛ.subset_ball (0 : Fin n → ℝ)
    obtain ⟨B, ε, k, hB, hε, hb⟩ :=
      hbound δ hδ (ball 0 r) isBounded_ball
    refine ⟨B, ε, k, hB, hε, fun T hT hsect z => ?_⟩
    obtain ⟨_, hrange, hhol, heq⟩ := hω T z hT
    obtain ⟨hAc, hAi⟩ := hA T hT z
    have hle : ∀ x ∈ Λ, ‖A T z x - ω T z (imaginarySlice x)‖ ≤ B * weight ε k T z :=
      norm_sub_le_of_dense_imaginary hIc hrange hhol.continuousOn heq hAc hr
        (hb T hT hsect z)
    exact fun x hx => ⟨hAi x, hle x hx⟩

end Langlands.Global.StandardParabolicFamily
