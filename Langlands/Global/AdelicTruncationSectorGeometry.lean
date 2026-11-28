import Langlands.Global.AdelicEisensteinTemperedTruncationEstimate
import Langlands.Analysis.TestedRegularSector

/-! # The regular truncation sectors in the actual coroot coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Set Filter MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct ContDiff Topology

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {m : ℕ} (eT : V fam.T ≃ₗ[ℝ] (Fin m → ℝ))

/-- The sector in the chosen real norm coordinates, restricted to the actual coroot space. -/
def truncationSector (δ : ℝ) : Set (Fin m → ℝ) :=
  {t | eT.symm t ∈ fam.coroots.realCorootSpan ∧
    ∀ α ∈ simpleRelativeRoots fam.i fam.ν, δ * ‖t‖ ≤ eval fam.T α (eT.symm t)}

omit [NumberField F] in
/-- A positive dilation preserves the sector inequalities and the coroot span. -/
theorem smul_mem_truncationSector {δ : ℝ} {t : Fin m → ℝ}
    (ht : t ∈ fam.truncationSector eT δ) {r : ℝ} (hr : 0 < r) :
    r • t ∈ fam.truncationSector eT δ := by
  refine ⟨by rw [map_smul]; exact fam.coroots.realCorootSpan.smul_mem r ht.1,
    fun α hα => ?_⟩
  have h := mul_le_mul_of_nonneg_left (ht.2 α hα) hr.le
  rw [map_smul, eval_eq_pair, map_smul, smul_eq_mul,
    norm_smul, Real.norm_of_nonneg hr.le]
  simpa only [mul_left_comm δ, ← eval_eq_pair] using h

omit [NumberField F] in
/-- Dilation by a factor at least one preserves a nonnegative root cutoff. -/
theorem isRegularTruncationParameter_smul {R : ℝ} (hR : 0 ≤ R)
    {T : V fam.T} (hT : fam.IsRegularTruncationParameter R T) {r : ℝ} (hr : 1 ≤ r) :
    fam.IsRegularTruncationParameter R (r • T) := by
  refine ⟨fam.coroots.realCorootSpan.smul_mem r hT.1, fun α hα => ?_⟩
  rw [eval_eq_pair, map_smul, smul_eq_mul, ← eval_eq_pair]
  exact (hT.2 α hα).trans (le_mul_of_one_le_left (hR.trans (hT.2 α hα)) hr)

omit [NumberField F] in
/-- The radial threshold on a positive sector implies the chosen lower root cutoff. -/
theorem isRegularTruncationParameter_of_mem_truncationSector {δ R : ℝ} (hδ : 0 < δ)
    {t : Fin m → ℝ} (ht : t ∈ fam.truncationSector eT δ) (hn : R / δ ≤ ‖t‖) :
    fam.IsRegularTruncationParameter R (eT.symm t) :=
  ⟨ht.1, fun α hα => ((div_le_iff₀ hδ).mp hn).trans
    (mul_comm δ ‖t‖ ▸ ht.2 α hα)⟩

omit [NumberField F] in
/-- When there is a simple root, the root cutoff can be increased once so every regular
truncation parameter has norm at least one in the chosen chart. -/
theorem exists_rootCutoff_for_one_le_norm (hroot : (simpleRelativeRoots fam.i fam.ν).Nonempty)
    (R₀ : ℝ) :
    ∃ R : ℝ, R₀ ≤ R ∧ 0 < R ∧
      ∀ T, fam.IsRegularTruncationParameter R T → 1 ≤ ‖eT T‖ := by
  obtain ⟨α, hα⟩ := hroot
  let L := (((pair fam.T) ((1 : ℝ) ⊗ₜ[ℤ] α)).comp eT.symm.toLinearMap).toContinuousLinearMap
  let R := max R₀ (‖L‖ + 1)
  have hR : ‖L‖ + 1 ≤ R := le_max_right _ _
  refine ⟨R, le_max_left _ _, (by positivity : 0 < ‖L‖ + 1).trans_le hR, ?_⟩
  intro T hT
  have hbound := L.le_opNorm (eT T)
  have heval : L (eT T) = eval fam.T α T := by
    change pair fam.T ((1 : ℝ) ⊗ₜ[ℤ] α) (eT.symm (eT T)) = _
    rw [eT.symm_apply_apply, eval_eq_pair]
  rw [heval, Real.norm_eq_abs] at hbound
  by_contra! hn
  have hle : R ≤ ‖L‖ * ‖eT T‖ :=
    (hT.2 α hα).trans ((le_abs_self _).trans hbound)
  have hn' : ‖L‖ * ‖eT T‖ ≤ ‖L‖ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn.le (norm_nonneg L)
  linarith [hle.trans hn', hR]

open Langlands.Global.AdelicGroupPoints in
/-- Comparable increments and tested vanishing imply the generic pointwise bound on a
truncation sector, with the same polynomial dependence on the central parameter. The
increment estimate may be uniform on a bounded set that meets the boundary of the generic
region. -/
theorem norm_le_of_tested_truncationIncrements {n nZ : ℕ}
    (eZ : RealCharacterDual F (fam.P fam.top) ≃ₗ[ℝ] (Fin nZ → ℝ))
    (dx : Measure (Fin n → ℝ)) [IsFiniteMeasureOnCompacts dx] [dx.IsOpenPosMeasure]
    (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (f : (Fin m → ℝ) → fam.positiveSplitComponent fam.top → (Fin n → ℝ) → ℂ)
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R)
    (hregNorm : ∀ T, fam.IsRegularTruncationParameter R T → 1 ≤ ‖eT T‖) :
    let C := fam.truncationSector eT δ
    let regular (t : Fin m → ℝ) := fam.IsRegularTruncationParameter R (eT.symm t)
    let l := comap (fun t : Fin m → ℝ => ‖t‖) atTop ⊓ 𝓟 C
    let weight (k : ℕ) (z : fam.positiveSplitComponent fam.top) :=
      1 + ‖eZ (characterLog F (fam.P fam.top) z.val)‖ ^ k
    (∀ z, ∀ᶠ t in l, ContinuousOn (f t z) U) →
    (∀ A ⊆ U, Bornology.IsBounded A → ∃ (B ε : ℝ) (k : ℕ), 0 ≤ B ∧ 0 < ε ∧
      ∀ z, ∀ x ∈ A, ∀ t ∈ C, ∀ s ∈ C, regular t → ‖s‖ ≤ ‖t‖ →
        dist (f t z x) (f (t + s) z x) ≤ B * Real.exp (-ε * ‖t‖) * weight k z) →
    (∀ z (β : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ U →
      Tendsto (fun t => ∫ x, β x • f t z x ∂dx) l (𝓝 0)) →
    ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
      ∃ (B ε : ℝ) (k : ℕ), 0 < B ∧ 0 < ε ∧
        ∀ z, ∀ x ∈ Λ ∩ U, ∀ t ∈ C, regular t →
          ‖f t z x‖ ≤ B * Real.exp (-ε * ‖t‖) * weight k z := by
  intro C regular l weight hc hinc htest Λ hΛ
  have hscale (t : Fin m → ℝ) (ht : t ∈ C) (r : ℝ) (hr : 0 < r) : r • t ∈ C :=
    fam.smul_mem_truncationSector eT ht hr
  have hn (t : Fin m → ℝ) (ht : regular t) : 1 ≤ ‖t‖ := by
    simpa only [eT.apply_symm_apply] using hregNorm (eT.symm t) ht
  by_cases hunit : ∃ u ∈ C, ‖u‖ = 1
  · let A := Λ ∩ U
    obtain ⟨B, ε, k, hB, hε, hstep⟩ :=
      hinc A inter_subset_right (hΛ.subset inter_subset_left)
    have hden : 0 < 1 - Real.exp (-ε) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hε))
    refine ⟨(B + 1) / (1 - Real.exp (-ε)), ε, k, div_pos (by linarith) hden, hε, ?_⟩
    intro z x hx t ht hreg
    have hw (j : ℕ) : 0 ≤ weight j z := by dsimp only [weight]; positivity
    have hcompar :
        ∀ S ⊆ U, IsCompact S → ∃ B' ε' : ℝ, 0 ≤ B' ∧ 0 < ε' ∧
          ∀ y ∈ S, ∀ v ∈ C, ∀ s ∈ C, regular v → 1 ≤ ‖v‖ → ‖s‖ ≤ ‖v‖ →
            dist (f v z y) (f (v + s) z y) ≤ B' * Real.exp (-ε' * ‖v‖) := by
      intro S hSU hSc
      obtain ⟨B', ε', k', hB', hε', hs⟩ := hinc S hSU hSc.isBounded
      refine ⟨B' * weight k' z, ε', mul_nonneg hB' (hw k'), hε', ?_⟩
      intro y hy v hv s hsC hvR _ hsn
      simpa only [mul_right_comm B'] using hs z y hy v hv s hsC hvR hsn
    have hregScale (v : Fin m → ℝ) (_ : v ∈ C) (hv : regular v) (r : ℝ)
        (hr : 1 ≤ r) : regular (r • v) := by
      change fam.IsRegularTruncationParameter R (eT.symm (r • v))
      rw [map_smul]
      exact fam.isRegularTruncationParameter_smul hR.le hv hr
    have htail : ∃ R' : ℝ, ∀ v ∈ C, R' ≤ ‖v‖ → regular v :=
      ⟨R / δ, fun _ hv hvr => fam.isRegularTruncationParameter_of_mem_truncationSector
        eT hδ hv hvr⟩
    have h := Langlands.Analysis.testedRegularSector dx C regular U (fun v y => f v z y)
      hunit hscale hregScale htail hU (hc z) hcompar (htest z)
      A inter_subset_right (B * weight k z) ε (mul_nonneg hB (hw k)) hε
      (fun y hy v hv s hs hvR _ hsn => by
        simpa only [mul_right_comm B] using hstep z y hy v hv s hs hvR hsn)
      x hx t ht hreg (hn t hreg)
    calc
      _ ≤ (B * weight k z) * Real.exp (-ε * ‖t‖) / (1 - Real.exp (-ε)) := h
      _ = (B / (1 - Real.exp (-ε))) * Real.exp (-ε * ‖t‖) * weight k z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) hden.le) (Real.exp_nonneg _)) (hw k)
  · refine ⟨1, 1, 0, zero_lt_one, zero_lt_one, fun z x hx t ht hreg => (hunit ?_).elim⟩
    have htpos : 0 < ‖t‖ := zero_lt_one.trans_le (hn t hreg)
    exact ⟨‖t‖⁻¹ • t, hscale t ht _ (inv_pos.mpr htpos), by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), inv_mul_cancel₀ htpos.ne']⟩

end Langlands.Global.StandardParabolicFamily
