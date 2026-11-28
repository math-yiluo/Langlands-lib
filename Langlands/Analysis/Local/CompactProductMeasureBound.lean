import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-! # A product-set volume bound for right-invariant measures -/

noncomputable section

universe u v

open MeasureTheory
open scoped ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.MeasureTheory

/-- The measure of a product with the image of a compact set is bounded by the
measures of two products thickened by an auxiliary compact set. -/
def CompactProductMeasureBoundStatement : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [T2Space G] [T2Space H] [SecondCountableTopology G] [SecondCountableTopology H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (mG : Measure G) (mH : Measure H) [SFinite mG] [SFinite mH]
    [mG.IsMulRightInvariant] [mH.IsMulRightInvariant]
    (i : H →* G), Continuous i →
    ∀ (D : Set G) (E V : Set H), IsCompact D → IsCompact E → IsCompact V →
      mH V * mG (D * i '' E) ≤ mG (D * i '' V⁻¹) * mH (V * E)

theorem compactProductMeasureBound : CompactProductMeasureBoundStatement.{u, v} := by
  classical
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ mG mH _ _ _ _ i hi D E V hD hE hV
  let P := D * i '' E
  let A := D * i '' V⁻¹
  let B := V * E
  have hPm : MeasurableSet P := (hD.mul (hE.image hi)).isClosed.measurableSet
  have hAm : MeasurableSet A := (hD.mul (hV.inv.image hi)).isClosed.measurableSet
  have hBm : MeasurableSet B := (hV.mul hE).isClosed.measurableSet
  let a : G → ℝ≥0∞ := A.indicator 1
  let b : H → ℝ≥0∞ := B.indicator 1
  have ha : Measurable a := measurable_const.indicator hAm
  have hb : Measurable b := measurable_const.indicator hBm
  let K (p : G × H) : ℝ≥0∞ := a (p.1 * (i p.2)⁻¹) * b p.2
  have hK : Measurable K :=
    (ha.comp (measurable_fst.mul ((hi.measurable.comp measurable_snd).inv))).mul
      (hb.comp measurable_snd)
  have hf (x : G) : P.indicator (fun _ => mH V) x ≤ ∫⁻ h, K (x, h) ∂mH := by
    by_cases hx : x ∈ P
    · rw [Set.indicator_of_mem hx]
      obtain ⟨d, hd, _, ⟨e, he, rfl⟩, rfl⟩ := hx
      let S := (fun h : H => h * e⁻¹) ⁻¹' V
      have hSm : MeasurableSet S := (measurable_mul_const _)
        (hV.isClosed.measurableSet)
      have hS : mH S = mH V :=
        (measurePreserving_mul_right mH e⁻¹).measure_preimage hV.isClosed.measurableSet.nullMeasurableSet
      rw [← hS, ← lintegral_indicator_one hSm]
      apply lintegral_mono
      intro h
      by_cases hh : h ∈ S
      · let v := h * e⁻¹
        have hv : v ∈ V := hh
        have hve : h = v * e := by
          dsimp only [v]
          rw [mul_assoc, inv_mul_cancel, mul_one]
        have hB : h ∈ B := hve ▸ Set.mul_mem_mul hv he
        have hA : (d * i e) * (i h)⁻¹ ∈ A := by
          rw [hve, map_mul, mul_inv_rev, mul_assoc d, mul_inv_cancel_left]
          exact Set.mul_mem_mul hd ⟨v⁻¹, by simpa only [Set.mem_inv, inv_inv] using hv, map_inv i v⟩
        simp only [Set.indicator_of_mem hh, K, a, b, Set.indicator_of_mem hA,
          Set.indicator_of_mem hB, Pi.one_apply, mul_one]
        exact le_rfl
      · simp only [Set.indicator_of_notMem hh, zero_le]
    · simp only [Set.indicator_of_notMem hx, zero_le]
  have hInner (h : H) : ∫⁻ x, K (x, h) ∂mG = mG A * b h := by
    change (∫⁻ x, a (x * (i h)⁻¹) * b h ∂mG) = _
    have hpres : ∫⁻ x, a (x * (i h)⁻¹) ∂mG = ∫⁻ x, a x ∂mG :=
      (measurePreserving_mul_right mG (i h)⁻¹).lintegral_comp ha
    have hmeas : Measurable (fun x => a (x * (i h)⁻¹)) := ha.comp (measurable_mul_const _)
    rw [lintegral_mul_const _ hmeas, hpres,
      show (∫⁻ x, a x ∂mG) = mG A from lintegral_indicator_one hAm]
  calc
    mH V * mG P = ∫⁻ x, P.indicator (fun _ => mH V) x ∂mG := by
      rw [lintegral_indicator hPm, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter]
    _ ≤ ∫⁻ x, ∫⁻ h, K (x, h) ∂mH ∂mG := lintegral_mono hf
    _ = ∫⁻ h, ∫⁻ x, K (x, h) ∂mG ∂mH := lintegral_lintegral_swap hK.aemeasurable
    _ = mG A * mH B := by
      simp_rw [hInner]
      rw [lintegral_const_mul _ hb, show (∫⁻ h, b h ∂mH) = mH B from lintegral_indicator_one hBm]

end Langlands.MeasureTheory
