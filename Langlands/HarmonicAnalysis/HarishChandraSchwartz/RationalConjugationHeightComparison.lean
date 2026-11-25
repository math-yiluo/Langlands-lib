import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompactHeightEnvelope
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConjugationBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay

/-! # Compact height comparisons for the conjugation integral -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

/-- Rapid decay for the integral of the absolute conjugation integrand
over the indicated family of integration regions. -/
def ConjugationComplementIntegralBound {G : Type*} [Group G] [MeasurableSpace G]
    (muG : Measure G) (T : Set G) (S : G → Set G) (f₁ f₂ : G → ℂ)
    (e σ : G → ℝ) : Prop :=
  ∀ r : ℝ, ∃ c : ℝ≥0, ∀ a ∈ T,
    ∫⁻ g in S a, ‖f₁ (a * g * a⁻¹)‖ₑ * ‖f₂ g‖ₑ ∂muG ≤
      c * ENNReal.ofReal (e a ^ 2 * (1 + σ a) ^ (-r))

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {K : Subgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

local notation "σ" => rationalHeight (F := F) ρ
local notation "τ" => rationalCompactHeight ρ K

include hKc

private theorem exists_rpow_one_add_rationalCompactHeight_bounds (r : ℝ) :
    ∃ A : ℝ≥0, (∀ g, (1 + σ g) ^ r ≤ (A : ℝ) * (1 + τ g) ^ r) ∧
      ∀ g, (1 + τ g) ^ r ≤ (A : ℝ) * (1 + σ g) ^ r := by
  obtain ⟨D, hD, hbound⟩ := rationalCompactHeight_bounds ρ K hKc
  let B : ℝ := 1 + 2 * D
  have hB : 1 ≤ B := by dsimp [B]; linarith
  let A : ℝ≥0 := Real.toNNReal (B ^ |r|)
  have hA : (A : ℝ) = B ^ |r| := Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _)
  have bounds (g : rationalPoints G) :
      0 < 1 + σ g ∧ 0 < 1 + τ g ∧
        1 + σ g ≤ B * (1 + τ g) ∧ 1 + τ g ≤ B * (1 + σ g) := by
    have hs : 0 < 1 + σ g := by linarith [rationalHeight_nonneg ρ g]
    have hle := add_le_add_right (hbound g).1 1
    have ht := hs.trans_le hle
    refine ⟨hs, ht, hle.trans ?_, (hbound g).2.2⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hB ht.le
  refine ⟨A, ?_, ?_⟩
  · intro g
    obtain ⟨hs, ht, hst, hts⟩ := bounds g
    rw [hA]
    exact rpow_le_rpow_abs_mul_of_le ht hs hB hts hst r
  · intro g
    obtain ⟨hs, ht, hst, hts⟩ := bounds g
    rw [hA]
    exact rpow_le_rpow_abs_mul_of_le hs ht hB hst hts r

/-- A conjugation height inequality for the original height also holds
for its compact envelope on the same regions. -/
theorem rationalCompactHeight_conjugationSigmaBound
    {T : Set (rationalPoints G)} {S : rationalPoints G → Set (rationalPoints G)}
    (h : ConjugationSigmaBound σ T S) :
    ConjugationSigmaBound τ T S := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨D, hD, hbound⟩ := rationalCompactHeight_bounds ρ K hKc
  refine ⟨(1 + 2 * D) * max C 0, fun a ha g hg => ?_⟩
  have hx := (hbound (a * g * a⁻¹)).1
  have hg' := (hbound g).1
  have hs : 0 ≤ 1 + σ g + σ (a * g * a⁻¹) := by
    linarith [rationalHeight_nonneg ρ g, rationalHeight_nonneg ρ (a * g * a⁻¹)]
  calc
    1 + τ a ≤ (1 + 2 * D) * (1 + σ a) := (hbound a).2.2
    _ ≤ (1 + 2 * D) * (C * (1 + σ g + σ (a * g * a⁻¹))) :=
      mul_le_mul_of_nonneg_left (hC a ha g hg) (by positivity)
    _ ≤ (1 + 2 * D) * (max C 0 * (1 + σ g + σ (a * g * a⁻¹))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hs) (by positivity)
    _ ≤ (1 + 2 * D) * (max C 0 * (1 + τ g + τ (a * g * a⁻¹))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)) (by positivity)
    _ = _ := by ring

private local instance : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

/-- Apply compact-invariant convolution weights to the complement and
express its rapid decay in the original matrix height. -/
theorem rationalConjugationComplementIntegralBound_of_compactHeight [CompactSpace K]
    {muG : Measure (rationalPoints G)} [SFinite muG]
    [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
    {Ξ e : rationalPoints G → ℝ} {T : Set (rationalPoints G)}
    {S : rationalPoints G → Set (rationalPoints G)}
    (hw : ConvolutionWeights muG K Ξ τ) (hup : XiUpperBound Ξ σ T e)
    (hgeom : ConjugationSigmaBound σ T S) {f₁ f₂ : rationalPoints G → ℂ}
    (hf₁ : ∀ r, nu Ξ σ r f₁ < ⊤) (hf₂ : ∀ r, nu Ξ σ r f₂ < ⊤) :
    ConjugationComplementIntegralBound muG T S f₁ f₂ e σ := by
  obtain ⟨D, hD, hbound⟩ := rationalCompactHeight_bounds ρ K hKc
  have hnonneg : 0 ≤ 1 + 2 * D := by positivity
  have hnu {f : rationalPoints G → ℂ} (hf : ∀ r, nu Ξ σ r f < ⊤) :
      ∀ r, nu Ξ τ r f < ⊤ :=
    all_nu_lt_top_of_one_add_height_le_mul hw.pos (rationalHeight_nonneg ρ) hw.nonneg
      hnonneg (fun g => (hbound g).2.2) hf
  have hright (k : rationalPoints G) (hk : k ∈ K) (g : rationalPoints G) :
      τ (g * k) = τ g := by
    simpa only [Subgroup.coe_one, one_mul] using rationalCompactHeight_mul_mul ρ K 1 ⟨k, hk⟩ g
  obtain ⟨C, d, hup⟩ := hup
  obtain ⟨A, hA, _⟩ := exists_rpow_one_add_rationalCompactHeight_bounds hKc ρ d
  have hup' : XiUpperBound Ξ τ T e := by
    refine ⟨C * (A : ℝ), d, fun a ha => ?_⟩
    have hs : 0 < 1 + σ a := by linarith [rationalHeight_nonneg ρ a]
    have hCe : 0 ≤ C * e a := nonneg_of_mul_nonneg_left
      ((hw.pos a).le.trans (hup a ha)) (Real.rpow_pos_of_pos hs d)
    calc
      Ξ a ≤ C * e a * (1 + σ a) ^ d := hup a ha
      _ ≤ C * e a * ((A : ℝ) * (1 + τ a) ^ d) := mul_le_mul_of_nonneg_left (hA a) hCe
      _ = _ := by ring
  intro r
  obtain ⟨c, hc⟩ := hw.lintegral_conj_mul_le hright hup'
    (rationalCompactHeight_conjugationSigmaBound hKc ρ hgeom) (hnu hf₁) (hnu hf₂) r
  obtain ⟨B, _, hB⟩ := exists_rpow_one_add_rationalCompactHeight_bounds hKc ρ (-r)
  refine ⟨c * B, fun a ha => (hc a ha).trans ?_⟩
  calc
    (c : ℝ≥0∞) * ENNReal.ofReal (e a ^ 2 * (1 + τ a) ^ (-r)) ≤
        (c : ℝ≥0∞) * ENNReal.ofReal ((B : ℝ) * (e a ^ 2 * (1 + σ a) ^ (-r))) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply ENNReal.ofReal_le_ofReal
      rw [mul_left_comm (B : ℝ)]
      exact mul_le_mul_of_nonneg_left (hB a) (sq_nonneg (e a))
    _ = _ := by rw [ENNReal.ofReal_mul B.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_mul, mul_assoc]

/-- The constant-term estimate also bounds the output in the restriction
of the ambient compact height. Its input weight keeps the original height. -/
theorem ConstantTermEstimate.rationalCompactHeight_output
    {M U : Subgroup (rationalPoints G)} {muU : Measure U} {δ : M →* ℝ≥0ˣ}
    {Ξ : rationalPoints G → ℝ} {ΞM : M → ℝ} (hΞM : ∀ m, 0 ≤ ΞM m)
    (h : ConstantTermEstimate muU δ Ξ σ ΞM (fun m : M => σ m)) :
    ConstantTermEstimate muU δ Ξ σ ΞM (fun m : M => τ m) := by
  intro d
  obtain ⟨d', c, hc⟩ := h d
  obtain ⟨A, hA, _⟩ := exists_rpow_one_add_rationalCompactHeight_bounds hKc ρ (-d)
  refine ⟨d', c * A, fun m => (hc m).trans ?_⟩
  calc
    (c : ℝ≥0∞) * ENNReal.ofReal (ΞM m * (1 + σ m) ^ (-d)) ≤
        (c : ℝ≥0∞) * ENNReal.ofReal ((A : ℝ) * (ΞM m * (1 + τ m) ^ (-d))) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply ENNReal.ofReal_le_ofReal
      rw [mul_left_comm (A : ℝ)]
      exact mul_le_mul_of_nonneg_left (hA m) (hΞM m)
    _ = _ := by rw [ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_mul, mul_assoc]

end Langlands.HarishChandraSchwartz
