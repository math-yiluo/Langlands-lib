import Langlands.Group.LeftQuotient
import Langlands.HarmonicAnalysis.AlgebraicIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Langlands.HarmonicAnalysis.AlgebraicIntegrand

/-!
# Pairing finite algebraic averages of functions on a coset space

A finite algebraic integral of functions `G → ℂ` is a finite combination of its values.
Integrating its product with a fixed function over `H \ G` therefore commutes with the
algebraic integral, provided each value gives an integrable product. No Fubini theorem
and no measurability of the averaging map are needed.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory QuotientIntegration HarmonicAnalysis

universe uG uX

variable {G : Type uG} [Group G] {H : Subgroup G} [MeasurableSpace (LeftQuotient H)]
variable {X : Type uX} [MeasurableSpace X]

/-- Pairing a finite algebraic integral of functions with a fixed function on `H \ G`,
using the representatives `q.out`. -/
theorem integral_pair_algebraicIntegral (μQ : Measure (LeftQuotient H)) (μ : Measure X)
    (f : SimpleFunc X (G → ℂ)) (hf : f.FinMeasSupp μ) (Ξ : G → ℂ)
    (hint : ∀ x, Integrable (fun q : LeftQuotient H => Ξ q.out * f x q.out) μQ) :
    ∫ q, Ξ q.out * AlgebraicIntegral.integral μ f q.out ∂μQ =
      ∫ x, ∫ q, Ξ q.out * f x q.out ∂μQ ∂μ := by
  classical
  set L : (G → ℂ) → ℂ := fun v => ∫ q, Ξ q.out * v q.out ∂μQ with hLdef
  have hL0 : L 0 = 0 := by simp [hLdef]
  have hR : ∫ x, L (f x) ∂μ = AlgebraicIntegral.integral μ (f.map L) := by
    rw [AlgebraicIntegral.integral_eq_bochner _ (hf.map hL0)]
    rfl
  change _ = ∫ x, L (f x) ∂μ
  rw [hR, AlgebraicIntegral.integral_map _ hf L hL0]
  unfold AlgebraicIntegral.integral
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [hLdef]
    simp only
    rw [← integral_const_mul]
    congr 1
    funext q
    ring
  · intro v hv
    obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.mp hv
    have := (hint x).const_mul ((μ (f ⁻¹' {f x})).toReal : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only
    ring

omit [MeasurableSpace (LeftQuotient H)] in
/-- A representative of `H g` differs from `g` by `H` on the left. -/
theorem out_mk_eq (g : G) : ∃ h : H, (Quotient.mk (QuotientGroup.rightRel H) g).out = h.val * g := by
  have h1 : Quotient.mk (QuotientGroup.rightRel H)
      (Quotient.mk (QuotientGroup.rightRel H) g).out = Quotient.mk _ g := Quotient.out_eq _
  have h2 : QuotientGroup.rightRel H _ _ := Quotient.exact h1
  rw [QuotientGroup.rightRel_apply] at h2
  refine ⟨⟨_, (inv_mem h2)⟩, ?_⟩
  simp [mul_assoc]

omit [MeasurableSpace (LeftQuotient H)] in
/-- A left `H`-invariant function takes the same value at `g` and at the representative
of `H g`. -/
theorem invariant_out_mk (Φ : G → ℂ) (hΦ : ∀ (h : H) g, Φ (h.val * g) = Φ g) (g : G) :
    Φ (Quotient.mk (QuotientGroup.rightRel H) g).out = Φ g := by
  obtain ⟨h, hh⟩ := out_mk_eq (H := H) g
  rw [hh, hΦ]

section Translation

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace (LeftQuotient H)]

/-- Right translation invariance of the quotient integral for a left invariant function. -/
theorem integral_out_mul_right (μQ : Measure (LeftQuotient H))
    (hμQ : ∀ g : G, MeasurePreserving (rightTranslate H g) μQ μQ)
    (Φ : G → ℂ) (hΦ : ∀ (h : H) g, Φ (h.val * g) = Φ g) (k : G) :
    ∫ q, Φ (q.out * k) ∂μQ = ∫ q, Φ q.out ∂μQ := by
  have hpt : ∀ q : LeftQuotient H, Φ (q.out * k) = Φ (rightTranslate H k q).out := by
    intro q
    conv_rhs => rw [← Quotient.out_eq q]
    rw [rightTranslate_mk, invariant_out_mk Φ hΦ]
  simp_rw [hpt]
  exact (hμQ k).integral_comp (rightTranslate H k).measurableEmbedding (fun q => Φ q.out)

end Translation

section Average

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
theorem rightTranslates_locallyConstant (F : G → ℂ) (L : OpenSubgroup G)
    (hF : ∀ g l, l ∈ L → F (g * l) = F g) :
    IsLocallyConstant (fun k : G => fun g => F (g * k)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro k
  refine ⟨(fun x => k⁻¹ * x) ⁻¹' (L : Set G),
    L.isOpen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro x hx
  funext g
  have hx' : k⁻¹ * x ∈ L := hx
  calc F (g * x) = F (g * k * (k⁻¹ * x)) := by group
    _ = F (g * k) := hF _ _ hx'

/-- The finite-image function `k ↦ w(k) • F(· k)`. -/
def rightTranslates (F : G → ℂ) (L : OpenSubgroup G) (hF : ∀ g l, l ∈ L → F (g * l) = F g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w) :
    SimpleFunc G (G → ℂ) :=
  compactlySupportedSimpleFunc (fun k => w k • fun g => F (g * k))
    (hw.comp₂ (rightTranslates_locallyConstant F L hF) (· • ·)) hwc.smul_right

/-- The weighted right average `g ↦ ∫ w(k) F(g k) dk` as an actual function. -/
def rightAverage (μG : Measure G) (F : G → ℂ) (L : OpenSubgroup G)
    (hF : ∀ g l, l ∈ L → F (g * l) = F g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w) : G → ℂ :=
  AlgebraicIntegral.integral μG (rightTranslates F L hF w hw hwc)

theorem rightAverage_apply (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (F : G → ℂ)
    (L : OpenSubgroup G) (hF : ∀ g l, l ∈ L → F (g * l) = F g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w) (g : G) :
    rightAverage μG F L hF w hw hwc g = ∫ k, w k * F (g * k) ∂μG := by
  have hfin : (rightTranslates F L hF w hw hwc).FinMeasSupp μG :=
    compactlySupportedSimpleFunc_finMeasSupp μG _ _ _
  have := AlgebraicIntegral.integral_linearMap _ hfin
    (LinearMap.proj (R := ℂ) (φ := fun _ : G => ℂ) g)
  calc rightAverage μG F L hF w hw hwc g =
      (LinearMap.proj (R := ℂ) (φ := fun _ : G => ℂ) g)
        (AlgebraicIntegral.integral μG (rightTranslates F L hF w hw hwc)) := rfl
    _ = _ := this.symm
    _ = ∫ k, w k * F (g * k) ∂μG := by
      rw [AlgebraicIntegral.integral_eq_bochner _ (hfin.map (LinearMap.proj g).map_zero)]
      congr 1

variable [BorelSpace (LeftQuotient H)]

/-- Pairing a right average with an equivariant function: if `Ξ(g k) = b(k) Ξ(g)` on the
support of `w`, the pairing is `(∫ w b⁻¹) ∫ Ξ F`. -/
theorem integral_pair_rightAverage (μQ : Measure (LeftQuotient H))
    (hμQ : ∀ g : G, MeasurePreserving (rightTranslate H g) μQ μQ)
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (F : G → ℂ)
    (L : OpenSubgroup G) (hF : ∀ g l, l ∈ L → F (g * l) = F g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w)
    (Ξ b : G → ℂ) (hΞ : ∀ g k, w k ≠ 0 → Ξ (g * k) = b k * Ξ g)
    (hb : ∀ k, w k ≠ 0 → b k ≠ 0)
    (hinv : ∀ (h : H) g, Ξ (h.val * g) * F (h.val * g) = Ξ g * F g)
    (hint : Integrable (fun q : LeftQuotient H => Ξ q.out * F q.out) μQ) :
    ∫ q, Ξ q.out * rightAverage μG F L hF w hw hwc q.out ∂μQ =
      (∫ k, w k * (b k)⁻¹ ∂μG) * ∫ q, Ξ q.out * F q.out ∂μQ := by
  have hfin : (rightTranslates F L hF w hw hwc).FinMeasSupp μG :=
    compactlySupportedSimpleFunc_finMeasSupp μG _ _ _
  have hk : ∀ k, ∫ q, Ξ q.out * (rightTranslates F L hF w hw hwc) k q.out ∂μQ =
      w k * (b k)⁻¹ * ∫ q, Ξ q.out * F q.out ∂μQ := by
    intro k
    by_cases hwk : w k = 0
    · simp [rightTranslates, hwk]
    · have hpt : ∀ q : LeftQuotient H, Ξ q.out * (rightTranslates F L hF w hw hwc) k q.out =
          w k * (b k)⁻¹ * (Ξ (q.out * k) * F (q.out * k)) := by
        intro q
        simp only [rightTranslates, compactlySupportedSimpleFunc_apply, Pi.smul_apply,
          smul_eq_mul]
        rw [hΞ _ _ hwk]
        field_simp [hb k hwk]
      simp_rw [hpt]
      rw [integral_const_mul,
        integral_out_mul_right μQ hμQ (fun g => Ξ g * F g) hinv k]
  have hintk : ∀ k, Integrable (fun q : LeftQuotient H =>
      Ξ q.out * (rightTranslates F L hF w hw hwc) k q.out) μQ := by
    intro k
    by_cases hwk : w k = 0
    · simp [rightTranslates, hwk]
    · have hpt : (fun q : LeftQuotient H => Ξ q.out * (rightTranslates F L hF w hw hwc) k q.out) =
          fun q => w k * (b k)⁻¹ * (Ξ (rightTranslate H k q).out * F (rightTranslate H k q).out) := by
        funext q
        simp only [rightTranslates, compactlySupportedSimpleFunc_apply, Pi.smul_apply,
          smul_eq_mul]
        conv_rhs => rw [← Quotient.out_eq q]
        rw [rightTranslate_mk, invariant_out_mk (fun g => Ξ g * F g) hinv]
        rw [hΞ _ _ hwk]
        field_simp [hb k hwk]
      rw [hpt]
      refine Integrable.const_mul ?_ _
      exact (hμQ k).integrable_comp_emb (rightTranslate H k).measurableEmbedding |>.mpr hint
  rw [rightAverage, integral_pair_algebraicIntegral μQ μG _ hfin Ξ hintk]
  simp_rw [hk]
  rw [integral_mul_const]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
theorem inverseTranslates_locallyConstant (F : G → ℂ) (L : OpenSubgroup G)
    (hF : ∀ g l, l ∈ L → F (g * l) = F g) :
    IsLocallyConstant (fun k : G => fun g => F (g * k⁻¹)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro k
  refine ⟨(fun x => x * k⁻¹) ⁻¹' (L : Set G),
    L.isOpen.preimage (continuous_id.mul continuous_const), by simp, ?_⟩
  intro x hx
  funext g
  have hx' : x * k⁻¹ ∈ L := hx
  calc F (g * x⁻¹) = F (g * k⁻¹ * (x * k⁻¹)⁻¹) := by group
    _ = F (g * k⁻¹) := hF _ _ (inv_mem hx')

/-- The finite-image function `k ↦ w(k) • F(· k⁻¹)`. -/
def inverseTranslates (F : G → ℂ) (L : OpenSubgroup G) (hF : ∀ g l, l ∈ L → F (g * l) = F g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w) :
    SimpleFunc G (G → ℂ) :=
  compactlySupportedSimpleFunc (fun k => w k • fun g => F (g * k⁻¹))
    (hw.comp₂ (inverseTranslates_locallyConstant F L hF) (· • ·)) hwc.smul_right

/-- The weighted inverse average `g ↦ ∫ w(k) F(g k⁻¹) dk`. -/
def inverseAverage (μG : Measure G) (F : G → ℂ) (L : OpenSubgroup G)
    (hF : ∀ g l, l ∈ L → F (g * l) = F g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w) : G → ℂ :=
  AlgebraicIntegral.integral μG (inverseTranslates F L hF w hw hwc)

/-- Adjointness of the two averages under the quotient integral: if the products
`F(g k) E(g)` are left `H`-invariant, then `∫ (avg F) E = ∫ F (inverse avg E)`. -/
theorem integral_rightAverage_pair (μQ : Measure (LeftQuotient H))
    (hμQ : ∀ g : G, MeasurePreserving (rightTranslate H g) μQ μQ)
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (F E : G → ℂ)
    (L L' : OpenSubgroup G) (hF : ∀ g l, l ∈ L → F (g * l) = F g)
    (hE : ∀ g l, l ∈ L' → E (g * l) = E g)
    (w : G → ℂ) (hw : IsLocallyConstant w) (hwc : HasCompactSupport w)
    (hinv : ∀ (h : H) g k, F (h.val * g * k) * E (h.val * g) = F (g * k) * E g)
    (hint : ∀ k, Integrable (fun q : LeftQuotient H => F q.out * E (q.out * k⁻¹)) μQ) :
    ∫ q, E q.out * rightAverage μG F L hF w hw hwc q.out ∂μQ =
      ∫ q, F q.out * inverseAverage μG E L' hE w hw hwc q.out ∂μQ := by
  have hfinR : (rightTranslates F L hF w hw hwc).FinMeasSupp μG :=
    compactlySupportedSimpleFunc_finMeasSupp μG _ _ _
  have hfinI : (inverseTranslates E L' hE w hw hwc).FinMeasSupp μG :=
    compactlySupportedSimpleFunc_finMeasSupp μG _ _ _
  have hswap : ∀ k, ∫ q, E q.out * F (q.out * k) ∂μQ = ∫ q, F q.out * E (q.out * k⁻¹) ∂μQ := by
    intro k
    have h1 := integral_out_mul_right μQ hμQ (fun g => F g * E (g * k⁻¹))
      (fun h g => by
        have := hinv h (g * k⁻¹) k
        simp only [mul_assoc, inv_mul_cancel, mul_one] at this
        simpa only [mul_assoc] using this) k
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h1
    rw [← h1]
    congr 1
    funext q
    ring
  have hintR : ∀ k, Integrable (fun q : LeftQuotient H =>
      E q.out * (rightTranslates F L hF w hw hwc) k q.out) μQ := by
    intro k
    have hpt : (fun q : LeftQuotient H => E q.out * (rightTranslates F L hF w hw hwc) k q.out) =
        fun q => w k * (F (rightTranslate H k q).out * E ((rightTranslate H k q).out * k⁻¹)) := by
      funext q
      simp only [rightTranslates, compactlySupportedSimpleFunc_apply, Pi.smul_apply,
        smul_eq_mul]
      conv_rhs => rw [← Quotient.out_eq q]
      rw [rightTranslate_mk]
      have := invariant_out_mk (H := H) (fun g => F g * E (g * k⁻¹))
        (fun h g => by
          have := hinv h (g * k⁻¹) k
          simp only [mul_assoc, inv_mul_cancel, mul_one] at this
          simpa only [mul_assoc] using this) (q.out * k)
      rw [this]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
      ring
    rw [hpt]
    exact ((hμQ k).integrable_comp_emb (rightTranslate H k).measurableEmbedding |>.mpr
      (hint k)).const_mul _
  have hintI : ∀ k, Integrable (fun q : LeftQuotient H =>
      F q.out * (inverseTranslates E L' hE w hw hwc) k q.out) μQ := by
    intro k
    have hpt : (fun q : LeftQuotient H => F q.out * (inverseTranslates E L' hE w hw hwc) k q.out) =
        fun q => w k * (F q.out * E (q.out * k⁻¹)) := by
      funext q
      simp only [inverseTranslates, compactlySupportedSimpleFunc_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [hpt]
    exact (hint k).const_mul _
  rw [rightAverage, integral_pair_algebraicIntegral μQ μG _ hfinR E hintR,
    inverseAverage, integral_pair_algebraicIntegral μQ μG _ hfinI F hintI]
  congr 1
  funext k
  simp only [rightTranslates, inverseTranslates, compactlySupportedSimpleFunc_apply,
    Pi.smul_apply, smul_eq_mul]
  have e1 : (fun q : LeftQuotient H => E q.out * (w k * F (q.out * k))) =
      fun q => w k * (E q.out * F (q.out * k)) := by funext q; ring
  have e2 : (fun q : LeftQuotient H => F q.out * (w k * E (q.out * k⁻¹))) =
      fun q => w k * (F q.out * E (q.out * k⁻¹)) := by funext q; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, hswap]

end Average

end Langlands.RankinSelberg.HighlyRamified
