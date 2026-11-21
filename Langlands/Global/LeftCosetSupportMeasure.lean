import Langlands.Global.LeftCosetWeilMeasure

/-! # Domination of a localized pushforward on a discrete left quotient -/

noncomputable section

universe u

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ : Subgroup H)

private theorem orbitMultiplicity_le {A D : Set H}
    (hD : ∀ a ∈ A, ∀ b ∈ A, a * b⁻¹ ∈ D) (x : H) :
    (∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) ≤
      ((Γ : Set H) ∩ D).encard := by
  classical
  let T : Set Γ := {γ | γ • x ∈ A}
  have hsum : (∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) = T.encard := by
    calc
      _ = ∑' γ : Γ, T.indicator 1 γ := by
        apply tsum_congr
        intro γ
        by_cases h : γ • x ∈ A <;> simp [T, h]
      _ = ∑' _ : T, (1 : ℝ≥0∞) := (tsum_subtype T 1).symm
      _ = (T.encard : ℝ≥0∞) := ENNReal.tsum_set_one T
  rw [hsum]
  by_cases hex : T.Nonempty
  · obtain ⟨γ₀, hγ₀⟩ := hex
    let e : Γ → H := fun γ => (γ : H) * (γ₀ : H)⁻¹
    have he : Function.Injective e := fun _ _ h => Subtype.ext (mul_right_cancel h)
    have hem : MapsTo e T ((Γ : Set H) ∩ D) := by
      intro γ hγ
      refine ⟨Γ.mul_mem γ.property (Γ.inv_mem γ₀.property), ?_⟩
      have h := hD (γ • x) hγ (γ₀ • x) hγ₀
      change ((γ : H) * x) * ((γ₀ : H) * x)⁻¹ ∈ D at h
      simpa [e, mul_assoc] using h
    exact ENat.toENNReal_mono (encard_le_encard_of_injOn hem he.injOn)
  · simp [not_nonempty_iff_eq_empty.mp hex]

/-- If `D` contains the quotients of pairs of points of `A`, and `B` contains
its image on the left quotient, pushforward of the ambient measure restricted to
`A` is dominated by the quotient measure restricted to `B` times `#(Γ ∩ D)`. -/
def LeftCosetSupportMeasureStatement : Prop :=
  ∀ {H : Type u} [Group H] (Γ : Subgroup H) [Countable Γ] [MeasurableSpace H]
    [MeasurableConstSMul Γ H] (μ : Measure H) [SMulInvariantMeasure Γ H μ]
    {s : Set H} (_hs : IsFundamentalDomain Γ s μ)
    {A D : Set H} (_hA : MeasurableSet A) {B : Set (LeftCosetSpace Γ)}
    (_hB : MeasurableSet B) (_hAB : mk Γ '' A ⊆ B)
    (_hD : ∀ a ∈ A, ∀ b ∈ A, a * b⁻¹ ∈ D),
      Measure.map (mk Γ) (μ.restrict A) ≤
        (((Γ : Set H) ∩ D).encard : ℝ≥0∞) • (quotientMeasure Γ μ s).restrict B

/-- Unfold the localized measure as a count of representatives in each orbit. -/
theorem leftCosetSupportMeasure : LeftCosetSupportMeasureStatement.{u} := by
  classical
  intro H _ Γ _ _ _ μ _ s hs A D hA B hB hAB hD
  let m : ℝ≥0∞ := ((Γ : Set H) ∩ D).encard
  apply Measure.le_iff.mpr
  intro V hV
  let E := mk Γ ⁻¹' V ∩ A
  have hE : MeasurableSet E := (measurable_mk Γ hV).inter hA
  let U := mk Γ ⁻¹' (V ∩ B)
  have hU : MeasurableSet U := measurable_mk Γ (hV.inter hB)
  have hpoint (x : H) :
      (∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x)) ≤
        U.indicator (fun _ => m) x := by
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      exact (ENNReal.tsum_le_tsum fun γ =>
        indicator_le_indicator_of_subset inter_subset_right (fun _ => zero_le) (γ • x)).trans
        (orbitMultiplicity_le Γ hD x)
    · have hz (γ : Γ) : γ • x ∉ E := by
        intro hγ
        have heq : mk Γ (γ • x) = mk Γ x := mk_subgroup_mul Γ γ x
        exact hx ⟨heq ▸ hγ.1, heq ▸ hAB (mem_image_of_mem (mk Γ) hγ.2)⟩
      simp [indicator_of_notMem, hz, hx]
  calc
    Measure.map (mk Γ) (μ.restrict A) V = μ E := by
      rw [Measure.map_apply (measurable_mk Γ) hV, Measure.restrict_apply (measurable_mk Γ hV)]
    _ = ∫⁻ x, E.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator hE, setLIntegral_const, one_mul]
    _ = ∫⁻ x in s, ∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (γ • x) ∂μ := by
      rw [hs.lintegral_eq_tsum'', lintegral_tsum]
      exact fun γ => ((measurable_const.indicator hE).comp (measurable_const_smul γ)).aemeasurable
    _ ≤ ∫⁻ x in s, U.indicator (fun _ => m) x ∂μ := lintegral_mono hpoint
    _ = (m • (quotientMeasure Γ μ s).restrict B) V := by
      rw [lintegral_indicator hU, setLIntegral_const, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply hV, quotientMeasure_apply Γ μ s (hV.inter hB),
        Measure.restrict_apply hU]

end Langlands.Global.LeftCosetSpace
