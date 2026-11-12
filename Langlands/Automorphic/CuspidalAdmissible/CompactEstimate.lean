import Langlands.Automorphic.CuspidalAdmissible.ExpConjugation
import Langlands.Automorphic.CuspidalAdmissible.CompactGeneric
import Langlands.Automorphic.CuspidalAdmissible.CuspIntegral
import Langlands.Automorphic.CuspidalL2.SiegelCover

/-!
# The square-integral estimate on a compact set

Let `φ` be a continuous function on the adelic group with smooth archimedean slices and
continuous basis derivatives `dφ_k`, right invariant under a compact open subgroup `L'` of the
finite adelic group. On a compact set `Kc`, for every `ε > 0`,

`∫_{Kc} |φ|² ≤ ε ∑_k ∫_{K₃} |dφ_k|² + C ∑_{p ∈ P} |A φ(p)|²`,

where `K₃` is a fixed compact set, `A φ` is the average over right translates by an
exponential box `U`, and `P` is a finite set; `U`, `P` and `C` depend only on `ε`, `Kc`, `L'`
and the measure. The average is close to `φ` in `L²(Kc)` (square-mean estimate along
exponentials and right invariance), and varies little on small exponential boxes
(conjugation of the exponential past `U` and left invariance), so finitely many values control
it on `Kc`.
-/

noncomputable section

universe u

open MeasureTheory NumberField Filter
open scoped Classical Topology ENNReal Pointwise Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

open ArchimedeanGL Langlands.Automorphic.CuspidalAdmissible

/-- Conjugation by `exp Z`, `‖Z‖ ≤ 1`, distorts norms by a bounded factor. -/
theorem exists_conj_norm_bound : ∃ CU : ℝ, 0 ≤ CU ∧ ∀ Z : ArchimedeanMatrix K n, ‖Z‖ ≤ 1 →
    ∀ Y : ArchimedeanMatrix K n,
      ‖(((archimedeanGLCoordinates K n (expInf K n Z))⁻¹ : ArchimedeanGL K n) :
          ArchimedeanMatrix K n) * Y *
        (archimedeanGLCoordinates K n (expInf K n Z) : ArchimedeanMatrix K n)‖ ≤ CU * ‖Y‖ := by
  set f : ArchimedeanMatrix K n → ℝ := fun Z =>
    ‖(((archimedeanGLCoordinates K n (expInf K n Z))⁻¹ : ArchimedeanGL K n) :
      ArchimedeanMatrix K n)‖ *
    ‖(archimedeanGLCoordinates K n (expInf K n Z) : ArchimedeanMatrix K n)‖ with hf
  have hfc : Continuous f :=
    ((Units.continuous_coe_inv.comp ((archimedeanGLCoordinates K n).continuous.comp
      (continuous_expInf K n))).norm).mul
    ((Units.continuous_val.comp ((archimedeanGLCoordinates K n).continuous.comp
      (continuous_expInf K n))).norm)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ArchimedeanMatrix K n) 1).exists_bound_of_continuousOn
    hfc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun Z hZ Y => ?_⟩
  have hZB : f Z ≤ max B 0 := by
    have := hB Z (by simpa using hZ)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  calc _ ≤ ‖(((archimedeanGLCoordinates K n (expInf K n Z))⁻¹ : ArchimedeanGL K n) :
          ArchimedeanMatrix K n) * Y‖ *
        ‖(archimedeanGLCoordinates K n (expInf K n Z) : ArchimedeanMatrix K n)‖ := norm_mul_le _ _
    _ ≤ ‖(((archimedeanGLCoordinates K n (expInf K n Z))⁻¹ : ArchimedeanGL K n) :
          ArchimedeanMatrix K n)‖ * ‖Y‖ *
        ‖(archimedeanGLCoordinates K n (expInf K n Z) : ArchimedeanMatrix K n)‖ := by
        gcongr
        exact norm_mul_le _ _
    _ = f Z * ‖Y‖ := by rw [hf]; ring
    _ ≤ max B 0 * ‖Y‖ := by gcongr

theorem expBox_mono {δ δ' : ℝ} (h : δ ≤ δ') (L : Set (FiniteAdelicGL K n)) :
    expBox K n δ L ⊆ expBox K n δ' L := by
  rintro _ ⟨⟨Z, l⟩, ⟨hZ, hl⟩, rfl⟩
  exact ⟨(Z, l), ⟨Metric.closedBall_subset_closedBall h hZ, hl⟩, rfl⟩

theorem ofInfinite_expInf_mem_expBox {δ : ℝ} {Z : ArchimedeanMatrix K n} (hZ : ‖Z‖ ≤ δ)
    {L : Subgroup (FiniteAdelicGL K n)} :
    AdelicGL.ofInfinite K n (expInf K n Z) ∈ expBox K n δ (L : Set (FiniteAdelicGL K n)) :=
  ⟨(Z, 1), ⟨by simpa using hZ, L.one_mem⟩, by
    show AdelicGL.ofInfinite K n (expInf K n Z) * AdelicGL.ofFinite K n 1 = _
    rw [map_one, mul_one]⟩

theorem one_mem_expBox {δ : ℝ} (hδ : 0 ≤ δ) {L : Subgroup (FiniteAdelicGL K n)} :
    (1 : AdelicGL K n) ∈ expBox K n δ (L : Set (FiniteAdelicGL K n)) := by
  have := ofInfinite_expInf_mem_expBox K n (Z := 0) (by simpa using hδ) (L := L)
  rwa [expInf_zero, map_one] at this

/-- **Smoothing error for one translate.** -/
theorem smoothing_bound [MeasurableSpace (AdelicGL K n)] [BorelSpace (AdelicGL K n)]
    [SecondCountableTopology (AdelicGL K n)] (ν : Measure (AdelicGL K n))
    [ν.IsMulRightInvariant] [SFinite ν] (L' : Subgroup (FiniteAdelicGL K n))
    (Kc : Set (AdelicGL K n)) {δ : ℝ} (hδ : δ ≤ 1) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (φ : AdelicGL K n → ℂ)
    (dφ : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → AdelicGL K n → ℂ)
    (hdφ : ∀ k, Continuous (dφ k))
    (hlevel : ∀ g, ∀ l ∈ L', φ (g * AdelicGL.ofFinite K n l) = φ g)
    (hexp : ∀ (x : AdelicGL K n) (Y : RealLieAlgebra K n),
      ‖φ (x * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y 1)) - φ x‖ₑ ^ 2 ≤
        ENNReal.ofReal ((Cb * ‖realLieAlgebraToMatrix K n Y‖) ^ 2) *
          ∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k
            (x * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y t))‖ₑ ^ 2) :
    ∀ u ∈ expBox K n δ (L' : Set (FiniteAdelicGL K n)),
      ∫⁻ g in Kc, ‖φ g - φ (g * u)‖ₑ ^ 2 ∂ν ≤
        ENNReal.ofReal ((Cb * δ) ^ 2) *
          ∑ k, ∫⁻ g in Kc * expBox K n 1 (L' : Set (FiniteAdelicGL K n)), ‖dφ k g‖ₑ ^ 2 ∂ν := by
  rintro _ ⟨⟨Z, l⟩, ⟨hZ, hl⟩, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right] at hZ
  set Y : RealLieAlgebra K n := (realLieAlgebraToMatrix K n).symm Z with hY
  have hYZ : realLieAlgebraToMatrix K n Y = Z := LinearEquiv.apply_symm_apply _ _
  set c : ℝ → AdelicGL K n := fun t => AdelicGL.ofInfinite K n (infiniteOneParameter K n Y t)
    with hc
  have hcc : Continuous c := (map_continuous (AdelicGL.ofInfinite K n)).comp
    (continuous_infiniteOneParameter K n Y)
  have hpt : ∀ g, ‖φ g - φ (g * (AdelicGL.ofInfinite K n (expInf K n Z) *
      AdelicGL.ofFinite K n l))‖ₑ ^ 2 ≤ ENNReal.ofReal ((Cb * δ) ^ 2) *
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (g * c t)‖ₑ ^ 2 := by
    intro g
    rw [← mul_assoc, hlevel _ l hl, enorm_sub_rev]
    refine (hexp g Y).trans ?_
    rw [hYZ]
    gcongr
  calc ∫⁻ g in Kc, ‖φ g - φ (g * (AdelicGL.ofInfinite K n (expInf K n Z) *
        AdelicGL.ofFinite K n l))‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ g in Kc, ENNReal.ofReal ((Cb * δ) ^ 2) *
          (∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (g * c t)‖ₑ ^ 2) ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal ((Cb * δ) ^ 2) *
          ∫⁻ g in Kc, (∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (g * c t)‖ₑ ^ 2) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        refine setLIntegral_right_translates_le ν Finset.univ dφ hdφ c hcc Kc _ ?_
        intro σ hσ g hg
        refine Set.mul_mem_mul hg ?_
        rw [hc]
        simp only
        rw [infiniteOneParameter_eq_expInf, hYZ]
        refine ofInfinite_expInf_mem_expBox K n ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
        nlinarith [hσ.1, hσ.2, norm_nonneg Z]

/-- **Equicontinuity of the average on small exponential boxes.** -/
theorem equicontinuity_bound [MeasurableSpace (AdelicGL K n)] [BorelSpace (AdelicGL K n)]
    (ν : Measure (AdelicGL K n)) [ν.IsMulLeftInvariant] [SFinite ν]
    [IsFiniteMeasureOnCompacts ν] (L' : Subgroup (FiniteAdelicGL K n))
    (hL'c : IsCompact (L' : Set (FiniteAdelicGL K n)))
    (Kc : Set (AdelicGL K n)) {δ η : ℝ} (hδ : δ ≤ 1) (hη : η ≤ 1)
    (hU0 : ν (expBox K n δ (L' : Set (FiniteAdelicGL K n))) ≠ 0)
    {CU : ℝ} (hCU0 : 0 ≤ CU) (hCU : ∀ Z : ArchimedeanMatrix K n, ‖Z‖ ≤ 1 →
      ∀ Y : ArchimedeanMatrix K n,
        ‖(((archimedeanGLCoordinates K n (expInf K n Z))⁻¹ : ArchimedeanGL K n) :
            ArchimedeanMatrix K n) * Y *
          (archimedeanGLCoordinates K n (expInf K n Z) : ArchimedeanMatrix K n)‖ ≤ CU * ‖Y‖)
    {Cb : ℝ} (hCb : 0 ≤ Cb) (φ : AdelicGL K n → ℂ) (hφ : Continuous φ)
    (dφ : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → AdelicGL K n → ℂ)
    (hdφ : ∀ k, Continuous (dφ k))
    (hlevel : ∀ g, ∀ l ∈ L', φ (g * AdelicGL.ofFinite K n l) = φ g)
    (hexp : ∀ (x : AdelicGL K n) (Y : RealLieAlgebra K n),
      ‖φ (x * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y 1)) - φ x‖ₑ ^ 2 ≤
        ENNReal.ofReal ((Cb * ‖realLieAlgebraToMatrix K n Y‖) ^ 2) *
          ∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k
            (x * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y t))‖ₑ ^ 2)
    {p : AdelicGL K n} (hp : p ∈ Kc) {w : AdelicGL K n}
    (hw : w ∈ expBox K n η (L' : Set (FiniteAdelicGL K n))) :
    ‖average ν (expBox K n δ (L' : Set (FiniteAdelicGL K n))) φ (p * w) -
        average ν (expBox K n δ (L' : Set (FiniteAdelicGL K n))) φ p‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Cb * CU * η) ^ 2) *
        (ν (expBox K n δ (L' : Set (FiniteAdelicGL K n))))⁻¹ *
        ∑ k, ∫⁻ g in Kc * expBox K n 1 (L' : Set (FiniteAdelicGL K n)) *
          expBox K n 1 (L' : Set (FiniteAdelicGL K n)), ‖dφ k g‖ₑ ^ 2 ∂ν := by
  have := adelicGL_t2Space K n
  set U := expBox K n δ (L' : Set (FiniteAdelicGL K n)) with hUdef
  set W₁ := expBox K n 1 (L' : Set (FiniteAdelicGL K n)) with hW₁def
  have hU : IsCompact U := isCompact_expBox K n δ hL'c
  have hUm : MeasurableSet U := hU.isClosed.measurableSet
  have hUW : U ⊆ W₁ := expBox_mono K n hδ _
  obtain ⟨⟨Zw, lw⟩, ⟨hZw, hlw⟩, rfl⟩ := hw
  simp only [Metric.mem_closedBall, dist_zero_right] at hZw
  have hlw' : lw ∈ L' := hlw
  set Yw : RealLieAlgebra K n := (realLieAlgebraToMatrix K n).symm Zw with hYw
  have hYwZ : realLieAlgebraToMatrix K n Yw = Zw := LinearEquiv.apply_symm_apply _ _
  set m : ℝ → AdelicGL K n := fun t => p *
    AdelicGL.ofInfinite K n (infiniteOneParameter K n Yw t) with hm
  have hmc : Continuous m := continuous_const.mul ((map_continuous (AdelicGL.ofInfinite K n)).comp
    (continuous_infiniteOneParameter K n Yw))
  -- the pointwise bound for `u ∈ U`
  have hpt : ∀ u ∈ U, ‖φ (p * (AdelicGL.ofInfinite K n (expInf K n Zw) *
      AdelicGL.ofFinite K n lw) * u) - φ (p * u)‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Cb * CU * η) ^ 2) *
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (m t * u)‖ₑ ^ 2 := by
    intro u hu
    obtain ⟨hlu, Zu, hZu, hinf⟩ := finite_mem_of_mem_expBox K n hu
    have hZu1 : ‖Zu‖ ≤ 1 := hZu.trans hδ
    set cc := archimedeanGLCoordinates K n (expInf K n Zu) with hcc
    set Z' : ArchimedeanMatrix K n :=
      ((cc⁻¹ : ArchimedeanGL K n) : ArchimedeanMatrix K n) * Zw * (cc : ArchimedeanMatrix K n)
      with hZ'
    set Y' : RealLieAlgebra K n := (realLieAlgebraToMatrix K n).symm Z' with hY'
    have hY'Z : realLieAlgebraToMatrix K n Y' = Z' := LinearEquiv.apply_symm_apply _ _
    -- removing the finite part of `w`
    have h1 : φ (p * (AdelicGL.ofInfinite K n (expInf K n Zw) * AdelicGL.ofFinite K n lw) * u) =
        φ (p * AdelicGL.ofInfinite K n (expInf K n Zw) * u) := by
      have heq : p * (AdelicGL.ofInfinite K n (expInf K n Zw) * AdelicGL.ofFinite K n lw) * u =
          p * AdelicGL.ofInfinite K n (expInf K n Zw) * u *
            (u⁻¹ * AdelicGL.ofFinite K n lw * u) := by group
      rw [heq, conj_ofFinite]
      exact hlevel _ _ (L'.mul_mem (L'.mul_mem (L'.inv_mem hlu) hlw') hlu)
    -- conjugating the exponential past `u`
    have hconj : ∀ t : ℝ, u⁻¹ * AdelicGL.ofInfinite K n (expInf K n (t • Zw)) * u =
        AdelicGL.ofInfinite K n (expInf K n (t • Z')) := by
      intro t
      rw [conj_ofInfinite, hinf, conj_expInf]
      congr 2
      rw [hZ', ← hcc, Matrix.mul_smul, Matrix.smul_mul]
    have h2 : p * AdelicGL.ofInfinite K n (expInf K n Zw) * u =
        p * u * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y' 1) := by
      have hc1 := hconj 1
      rw [one_smul, one_smul] at hc1
      rw [infiniteOneParameter_eq_expInf, hY'Z, one_smul, ← hc1]
      group
    have h3 : ∀ t, p * u * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y' t) = m t * u := by
      intro t
      rw [infiniteOneParameter_eq_expInf, hY'Z, ← hconj t, hm]
      simp only
      rw [infiniteOneParameter_eq_expInf, hYwZ]
      group
    have hnorm : ‖Z'‖ ≤ CU * η :=
      (hCU Zu hZu1 Zw).trans (mul_le_mul_of_nonneg_left hZw hCU0)
    rw [h1, h2]
    refine (hexp (p * u) Y').trans ?_
    rw [hY'Z]
    simp only [h3]
    have hle : Cb * ‖Z'‖ ≤ Cb * CU * η := by
      calc Cb * ‖Z'‖ ≤ Cb * (CU * η) := mul_le_mul_of_nonneg_left hnorm hCb
        _ = Cb * CU * η := by ring
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (mul_nonneg hCb (norm_nonneg _)) hle 2)) le_rfl
  -- integrating against the normalized measure
  calc ‖average ν U φ (p * (AdelicGL.ofInfinite K n (expInf K n Zw) *
        AdelicGL.ofFinite K n lw)) - average ν U φ p‖ₑ ^ 2
      ≤ ∫⁻ u, ‖φ (p * (AdelicGL.ofInfinite K n (expInf K n Zw) *
          AdelicGL.ofFinite K n lw) * u) - φ (p * u)‖ₑ ^ 2 ∂avgMeasure ν U :=
        enorm_average_sub_sq_le ν hU hU0 hφ p _
    _ = (ν U)⁻¹ * ∫⁻ u in U, ‖φ (p * (AdelicGL.ofInfinite K n (expInf K n Zw) *
          AdelicGL.ofFinite K n lw) * u) - φ (p * u)‖ₑ ^ 2 ∂ν := by
        rw [avgMeasure, lintegral_smul_measure, smul_eq_mul]
    _ ≤ (ν U)⁻¹ * ∫⁻ u in U, ENNReal.ofReal ((Cb * CU * η) ^ 2) *
          (∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (m t * u)‖ₑ ^ 2) ∂ν := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' hUm hpt)
    _ = (ν U)⁻¹ * (ENNReal.ofReal ((Cb * CU * η) ^ 2) *
          ∫⁻ u in U, (∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (m t * u)‖ₑ ^ 2) ∂ν) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ (ν U)⁻¹ * (ENNReal.ofReal ((Cb * CU * η) ^ 2) *
          ∑ k, ∫⁻ g in Kc * W₁ * W₁, ‖dφ k g‖ₑ ^ 2 ∂ν) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        refine setLIntegral_translates_le ν Finset.univ dφ hdφ m hmc U _ ?_
        intro σ hσ u hu
        refine Set.mul_mem_mul (Set.mul_mem_mul hp ?_) (hUW hu)
        rw [infiniteOneParameter_eq_expInf, hYwZ]
        refine ofInfinite_expInf_mem_expBox K n ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
        nlinarith [hσ.1, hσ.2, norm_nonneg Zw, hZw.trans hη]
    _ = _ := by ring

/-- `a x² ≤ ε / k` once `0 ≤ x ≤ min 1 (ε / (k (a + 1)))`. -/
theorem mul_sq_le_of_le_div {a ε k x : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hk : 0 < k)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hx : x ≤ ε / (k * (a + 1))) : a * x ^ 2 ≤ ε / k := by
  have h1 : a * x ^ 2 ≤ a * x := mul_le_mul_of_nonneg_left (by nlinarith) ha
  have h2 : a * x ≤ a * (ε / (k * (a + 1))) := mul_le_mul_of_nonneg_left hx ha
  have h3 : a * (ε / (k * (a + 1))) ≤ ε / k := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hk]
    nlinarith [hε.le, hk.le]
  linarith

set_option maxHeartbeats 2000000 in
/-- **The compact estimate.** -/
theorem exists_compact_estimate [MeasurableSpace (AdelicGL K n)] [BorelSpace (AdelicGL K n)]
    [SecondCountableTopology (AdelicGL K n)] (ν : Measure (AdelicGL K n))
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] [SFinite ν] (L' : Subgroup (FiniteAdelicGL K n))
    (hL'o : IsOpen (L' : Set (FiniteAdelicGL K n)))
    (hL'c : IsCompact (L' : Set (FiniteAdelicGL K n)))
    (Kc : Set (AdelicGL K n)) (hKc : IsCompact Kc) :
    ∃ K₃ : Set (AdelicGL K n), IsCompact K₃ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ (U : Set (AdelicGL K n)) (P : Finset (AdelicGL K n)) (C : ℝ≥0∞),
        IsCompact U ∧ ν U ≠ 0 ∧ C ≠ ⊤ ∧
        ∀ (φ : AdelicGL K n → ℂ)
          (dφ : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → AdelicGL K n → ℂ),
          Continuous φ → (∀ k, Continuous (dφ k)) →
          (∀ g, ∀ l ∈ L', φ (g * AdelicGL.ofFinite K n l) = φ g) →
          (∀ y : FiniteAdelicGL K n, ∃ s : SmoothFunctions K n,
            (∀ g, s.val g = φ (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) ∧
            ∀ k g, (smoothDifferential K n (lieDirection K n k) s).val g =
              dφ k (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) →
          ∫⁻ g in Kc, ‖φ g‖ₑ ^ 2 ∂ν ≤
            ENNReal.ofReal ε * ∑ k, ∫⁻ g in K₃, ‖dφ k g‖ₑ ^ 2 ∂ν +
              C * ∑ p ∈ P, ‖average ν U φ p‖ₑ ^ 2 := by
  have := adelicGL_t2Space K n
  obtain ⟨Cb, hCb, hexpAll⟩ := exists_exp_pointwise K n
  obtain ⟨CU, hCU0, hCU⟩ := exists_conj_norm_bound K n
  set W₁ := expBox K n 1 (L' : Set (FiniteAdelicGL K n)) with hW₁def
  have hW₁ : IsCompact W₁ := isCompact_expBox K n 1 hL'c
  have h1W : (1 : AdelicGL K n) ∈ W₁ := one_mem_expBox K n zero_le_one
  have hKW : Kc * W₁ ⊆ Kc * W₁ * W₁ := fun g hg => ⟨g, hg, 1, h1W, mul_one g⟩
  refine ⟨Kc * W₁ * W₁, (hKc.mul hW₁).mul hW₁, fun ε hε => ?_⟩
  set δ : ℝ := min 1 (ε / (4 * (Cb ^ 2 + 1))) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  set U := expBox K n δ (L' : Set (FiniteAdelicGL K n)) with hUdef
  have hU : IsCompact U := isCompact_expBox K n δ hL'c
  have hL'n : (L' : Set (FiniteAdelicGL K n)) ∈ 𝓝 1 := hL'o.mem_nhds L'.one_mem
  have hU0 : ν U ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds (μ := ν) (expBox_mem_nhds K n hδpos hL'n)).ne'
  have hKfin : ν Kc ≠ ⊤ := hKc.measure_lt_top.ne
  have hfin : 4 * ν Kc * (ν U)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hKfin) (ENNReal.inv_ne_top.mpr hU0)
  set c₀ : ℝ := (4 * ν Kc * (ν U)⁻¹).toReal with hc₀
  have hc₀0 : 0 ≤ c₀ := ENNReal.toReal_nonneg
  set η : ℝ := min 1 (ε / (2 * (c₀ * (Cb * CU) ^ 2 + 1))) with hηdef
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  obtain ⟨P, hPK, hnet⟩ := exists_finite_net hKc (expBox_mem_nhds K n hηpos hL'n)
  refine ⟨U, P, 4 * ν Kc, hU, hU0, ENNReal.mul_ne_top ENNReal.ofNat_ne_top hKfin,
    fun φ dφ hφ hdφ hlevel hslice => ?_⟩
  have hexp := hexpAll φ dφ hdφ hslice
  set E := ∑ k, ∫⁻ g in Kc * W₁ * W₁, ‖dφ k g‖ₑ ^ 2 ∂ν with hE
  set r : ℝ≥0∞ := ENNReal.ofReal ((Cb * δ) ^ 2) with hr
  set q : ℝ≥0∞ := ENNReal.ofReal ((Cb * CU * η) ^ 2) * (ν U)⁻¹ with hq
  set Sp := ∑ p ∈ P, ‖average ν U φ p‖ₑ ^ 2 with hSp
  -- the smoothing error
  have ha : ∀ u ∈ U, ∫⁻ g in Kc, ‖φ g - φ (g * u)‖ₑ ^ 2 ∂ν ≤ r * E := fun u hu =>
    (smoothing_bound K n ν L' Kc hδ1 hCb φ dφ hdφ hlevel hexp u hu).trans
      (mul_le_mul' le_rfl (Finset.sum_le_sum fun k _ => lintegral_mono_set hKW))
  have hsmooth := lintegral_sub_average_le ν hU hU0 hφ Kc _ ha
  -- the average is controlled by finitely many values on `Kc`
  have hpt : ∀ g ∈ Kc, ‖average ν U φ g‖ₑ ^ 2 ≤ 2 * Sp + 2 * (q * E) := by
    intro g hg
    obtain ⟨p, hp, w, hw, rfl⟩ := hnet g hg
    have h1 := enorm_sq_le_two_mul (average ν U φ (p * w)) (average ν U φ p)
    have h2 := equicontinuity_bound K n ν L' hL'c Kc hδ1 hη1 hU0 hCU0 hCU hCb φ hφ dφ hdφ
      hlevel hexp (hPK hp) hw
    have h3 : ‖average ν U φ p‖ₑ ^ 2 ≤ Sp :=
      Finset.single_le_sum (f := fun p => ‖average ν U φ p‖ₑ ^ 2) (fun _ _ => zero_le) hp
    calc ‖average ν U φ (p * w)‖ₑ ^ 2 ≤ 2 * ‖average ν U φ p‖ₑ ^ 2 +
          2 * ‖average ν U φ (p * w) - average ν U φ p‖ₑ ^ 2 := h1
      _ ≤ 2 * Sp + 2 * (ENNReal.ofReal ((Cb * CU * η) ^ 2) * (ν U)⁻¹ * E) := by gcongr
  -- the coefficient bound
  have hcoef : ν Kc * (2 * (2 * q)) + 2 * r ≤ ENNReal.ofReal ε := by
    have h4 : 4 * ν Kc * (ν U)⁻¹ = ENNReal.ofReal c₀ := (ENNReal.ofReal_toReal hfin).symm
    have e1 : ν Kc * (2 * (2 * q)) = ENNReal.ofReal (c₀ * (Cb * CU * η) ^ 2) := by
      rw [ENNReal.ofReal_mul hc₀0, ← h4, hq]
      ring
    have e2 : 2 * r = ENNReal.ofReal (2 * (Cb * δ) ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), hr, ENNReal.ofReal_ofNat]
    rw [e1, e2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have b1 : c₀ * (Cb * CU) ^ 2 * η ^ 2 ≤ ε / 2 :=
      mul_sq_le_of_le_div (by positivity) hε (by norm_num) hηpos.le hη1 (by
        rw [hηdef]; exact min_le_right _ _)
    have b2 : Cb ^ 2 * δ ^ 2 ≤ ε / 4 :=
      mul_sq_le_of_le_div (by positivity) hε (by norm_num) hδpos.le hδ1 (by
        rw [hδdef]; exact min_le_right _ _)
    nlinarith [b1, b2]
  -- assembling
  have hKm : MeasurableSet Kc := hKc.isClosed.measurableSet
  calc ∫⁻ g in Kc, ‖φ g‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ g in Kc, (2 * (2 * Sp + 2 * (q * E)) +
          2 * ‖φ g - average ν U φ g‖ₑ ^ 2) ∂ν := by
        refine setLIntegral_mono' hKm fun g hg => ?_
        refine (enorm_sq_le_two_mul (φ g) (average ν U φ g)).trans ?_
        gcongr
        exact hpt g hg
    _ = ν Kc * (2 * (2 * Sp + 2 * (q * E))) +
          2 * ∫⁻ g in Kc, ‖φ g - average ν U φ g‖ₑ ^ 2 ∂ν := by
        rw [lintegral_add_left measurable_const, setLIntegral_const,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, mul_comm (ν Kc)]
    _ ≤ ν Kc * (2 * (2 * Sp + 2 * (q * E))) + 2 * (r * E) := by gcongr
    _ = (ν Kc * (2 * (2 * q)) + 2 * r) * E + 4 * ν Kc * Sp := by ring
    _ ≤ ENNReal.ofReal ε * E + 4 * ν Kc * Sp := by gcongr

end Langlands.Global
