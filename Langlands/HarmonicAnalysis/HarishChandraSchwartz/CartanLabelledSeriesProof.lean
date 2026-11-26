import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CartanLabelledSeriesStatement
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof
import Langlands.Representation.Hecke.DoubleCoset

/-! # Proof of the bounded-multiplicity Cartan series comparison -/

universe u

open MeasureTheory
open scoped ENNReal

namespace Langlands.HarishChandraSchwartz

open QuotientIntegration

/-- The corrected Cartan sum is bounded in both directions under the
published target's explicit disjointness and covering hypotheses. -/
theorem cartanLabelledSeries : CartanLabelledSeriesStatement.{u} := by
  intro G _ _ _ C hC K₀ K hK P F S _ _ hSP hStable hTrans hDisjoint r k hk
  let coarse (t : F × S) :=
    leftQuotientMap C '' DoubleCoset.doubleCoset (t.2.val * t.1.val) K₀ K₀
  let cell (p : Fin r × Fin r) (t : F × S) :=
    leftQuotientMap C '' DoubleCoset.doubleCoset (k p.1 * (t.2.val * t.1.val) * k p.2) K K
  have hCoarse : Pairwise (fun t t' => Disjoint (coarse t) (coarse t')) := by
    intro t t' htt'
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hq⟩
    let c : C := ⟨y * x⁻¹, QuotientGroup.rightRel_apply.mp (Quotient.exact hq.symm)⟩
    have hcx : (c : G) * x = y := by
      change (y * x⁻¹) * x = y
      exact inv_mul_cancel_right y x
    have hcent (w : G) : w * (c : G) = (c : G) * w :=
      Subgroup.mem_center_iff.mp (hC c.property) w
    have hy' : y ∈ DoubleCoset.doubleCoset ((t.2.val * (c : G)) * t.1.val) K₀ K₀ := by
      obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mem_doubleCoset.mp hx
      refine DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b, hb, ?_⟩
      rw [← hcx, hab]
      simp only [← mul_assoc]
      rw [← hcent a, mul_assoc a (c : G) t.2.val, ← hcent t.2.val, ← mul_assoc]
    have hcoset :=
      (DoubleCoset.doubleCoset_eq_of_mem hy').symm.trans (DoubleCoset.doubleCoset_eq_of_mem hy)
    obtain ⟨hf, hz⟩ := hDisjoint _ t.1.property _ t'.1.property _
      (hStable _ (hSP t.2.property) _ c.property) _ (hSP t'.2.property) hcoset
    have hqz : leftQuotientMap C t.2.val = leftQuotientMap C t'.2.val := by
      rw [← hz, hcent t.2.val, leftQuotientMap_subgroup_mul]
    exact htt' (Prod.ext (Subtype.ext hf)
      (Subtype.ext (hTrans t.2.property t'.2.property hqz)))
  have hSub (p : Fin r × Fin r) (t : F × S) : cell p t ⊆ coarse t := by
    apply Set.image_mono
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨a * k p.1, K₀.mul_mem (hK ha) (hk p.1), k p.2 * b, K₀.mul_mem (hk p.2) (hK hb), by group⟩
  refine ⟨hCoarse, ?_⟩
  intro _ _ μ a
  have hMeas (p : Fin r × Fin r) (t : F × S) : MeasurableSet (cell p t) :=
    ((leftQuotient_isOpenQuotientMap C).isOpenMap _
      (Hecke.TestFunction.isOpen_doubleCosetSet K (k p.1 * (t.2.val * t.1.val) * k p.2))).measurableSet
  have hFixed (p : Fin r × Fin r) :
      (∑' t, ∫⁻ x in cell p t, a x ∂μ) ≤ ∫⁻ x, a x ∂μ := by
    have hd : Pairwise (fun t t' => Disjoint (cell p t) (cell p t')) :=
      fun t t' ht => (hCoarse ht).mono (hSub p t) (hSub p t')
    rw [← lintegral_iUnion (hMeas p) hd a]
    exact setLIntegral_le_lintegral _ _
  constructor
  · calc
      (∑' p, ∑' t, ∫⁻ x in cell p t, a x ∂μ) ≤ ∑' _ : Fin r × Fin r, ∫⁻ x, a x ∂μ :=
        ENNReal.tsum_le_tsum hFixed
      _ = (r : ℝ≥0∞) ^ 2 * ∫⁻ x, a x ∂μ := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Fintype.card_fin, Nat.cast_mul, pow_two]
  · intro hCover
    change (⋃ p, ⋃ t, cell p t) = Set.univ at hCover
    have hUpper : (∫⁻ x, a x ∂μ) ≤ ∑' p, ∫⁻ x in ⋃ t, cell p t, a x ∂μ := by
      simpa only [hCover, Measure.restrict_univ] using
        (lintegral_iUnion_le (μ := μ) (fun p => ⋃ t, cell p t) a)
    exact hUpper.trans (ENNReal.tsum_le_tsum fun p =>
      lintegral_iUnion_le (μ := μ) (cell p) a)

end Langlands.HarishChandraSchwartz
