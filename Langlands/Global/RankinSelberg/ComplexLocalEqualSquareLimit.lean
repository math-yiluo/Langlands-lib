import Langlands.Analysis.Complex.AffineStripExtension
import Langlands.Global.RankinSelberg.ComplexLocalEqualSquareTraceBounds
import Langlands.Global.RankinSelberg.ComplexLocalSquareFourierSchwartz
import Langlands.Global.RankinSelberg.ComplexUnitarySchwartzDensity

/-! # The normalized equal-rank square limit for arbitrary Schwartz tests -/

noncomputable section

open Filter MeasureTheory
open Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear Langlands.GodementJacquet
open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Elementwise SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (shiftedCharacter)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Test" => 𝓢(Mat, ℂ)
local notation "gap" => Nat.lt_succ_self r
local notation "ud" => ArchimedeanLocal.dualFunction m
local notation "wd" => ArchimedeanLocal.dualFunction n

private theorem eventually_weight_sub {X : Type*} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {Φ : X} {Ψ : ℕ → X} (hΨ : Tendsto Ψ atTop (𝓝 Φ))
    {p : X → ℝ} (hp : Continuous p) (hp₀ : p 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → p (Ψ i - Ψ j) ≤ ε := by
  have ht : Tendsto (fun q : ℕ × ℕ => Ψ q.1 - Ψ q.2) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using
      (hΨ.comp tendsto_fst).sub (hΨ.comp tendsto_snd)
  have h' := hp.continuousAt.tendsto.comp ht
  rw [hp₀] at h'
  have he := h'.eventually (eventually_lt_nhds hε)
  rw [prod_atTop_atTop_eq] at he
  obtain ⟨⟨i₀, j₀⟩, h⟩ := eventually_atTop.mp he
  exact ⟨max i₀ j₀, fun i j hi hj =>
    (h (i, j) ⟨(le_max_left _ _).trans hi, (le_max_right _ _).trans hj⟩).le⟩

private theorem tendsto_of_trace_bound {X : Type*} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {Φ : X} {Ψ : ℕ → X} (hΨ : Tendsto Ψ atTop (𝓝 Φ))
    {p : X → ℝ} (hp : Continuous p) (hp₀ : p 0 = 0)
    {J : X → ℂ} {C : ℝ} (hJ : ∀ x y, ‖J x - J y‖ ≤ p (x - y) * C) :
    Tendsto (fun i => J (Ψ i)) atTop (𝓝 (J Φ)) := by
  have ht : Tendsto (fun i => Ψ i - Φ) atTop (𝓝 0) := by
    simpa only [sub_self] using hΨ.sub (tendsto_const_nhds (x := Φ))
  have h' := (hp.continuousAt.tendsto.comp ht).mul_const C
  rw [hp₀, zero_mul] at h'
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun i => hJ (Ψ i) Φ) h')

private theorem tilt_exponential_bound {ε δ K₀ L₀ K L : ℝ} {v s z t : ℂ}
    (hε : 0 ≤ ε) (hδ : δ ≤ ε) (hL₀ : 0 ≤ L₀)
    (hK : K₀ + L₀ ≤ K) (hL : L₀ ≤ L)
    (ht : |t.im| = |s.im|) (hz : |z.im| ≤ |v.im| + |s.im|) :
    δ * Real.exp (K₀ * |t.im| + L₀ * |z.im|) ≤
      ε * Real.exp (K * |s.im| + L * |v.im|) := by
  rw [ht]
  refine mul_le_mul hδ (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hε
  linarith [mul_le_mul_of_nonneg_left hz hL₀, mul_le_mul_of_nonneg_right hK (abs_nonneg s.im),
    mul_le_mul_of_nonneg_right hL (abs_nonneg v.im)]

/-- The finite normalized products give an entire limit along parameter curves for every
square Schwartz test, with both normalized chamber traces and fixed-parameter strip growth. -/
def ComplexLocalEqualSquareLimitStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData), ds.length = m →
  ∀ (e : Fin n → ComplexCharacterData) (U : complexWhittakerModel r ds 1)
    (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ)),
    IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-1) B →
  ∀ (f : complexStandardKFinite n (List.ofFn e)) (Ψ Ψd : Test),
    (Ψd : Mat → ℂ) = complexMatrixFourier 1 Ψ →
    (∀ V : complexWhittakerModel (r + 1) (List.ofFn e) (-1),
      HasComplexPairNormalizedGrowth (List.ofFn e) ds (-1) (complexCentralSign ds ^ m)
        (complexUnequalIntegral gap D₁ V.val U.val)
        (complexUnequalDualIntegral gap (-1) D₁ V.val U.val)) →
    ∃ F : ℂ × ℂ → ℂ,
      (∀ γ : ℂ → ℂ × ℂ, Differentiable ℂ γ → Differentiable ℂ (F ∘ γ)) ∧
      (∀ z : ℂ, HasStripExponentialGrowth (fun s => F (z, s))) ∧
      (∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
        F (z, s) = equalDoubleDenominator d ds (List.ofFn e) z s *
          complexEqualUnfoldedIntegral D.groupHaar D₁
            (shiftedCharacter d z).character.toMonoidHom Ψ U.val (B f) s) ∧
      (∃ τ σ : ℝ, ∀ z s : ℂ, τ < (-z).re → σ < s.re →
        F (z, 1 - s) = (equalDoublePhase d ds (List.ofFn e))⁻¹ *
          (equalDoubleDualDenominator d ds (List.ofFn e) z s *
            complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d.inv (-z)).character.toMonoidHom
              Ψd (ud U.val) (wd (B f)) s))

set_option maxHeartbeats 1500000 in
theorem complexLocalEqualSquareLimit : ComplexLocalEqualSquareLimitStatement (r := r) := by
  intro D D₁ d ds hds e U B hB f Ψ Ψd hΨd hAdj
  let es := List.ofFn e
  have hes : es.length = n := List.length_ofFn
  let V : complexWhittakerModel (r + 1) es (-1) :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let Ud : complexWhittakerModel r (dualData ds) (-1) := ⟨ud U.val, dualFunction_mem hds U.2⟩
  let Vd : complexWhittakerModel (r + 1) (dualData es) (-(-1 : ℂˣ)) :=
    ⟨wd V.val, dualFunction_mem hes V.2⟩
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite D.groupHaar := complexLocalGroupHaarSigmaFinite D
  let : SigmaFinite D₁.measure := complexLocalQuotientSigmaFinite D₁
  obtain ⟨T, hT⟩ := (complexLocalSquareFourierSchwartz : ComplexLocalSquareFourierSchwartzStatement n) 1
  have hΨd' : Ψd = T Ψ := by
    ext X
    exact congrFun (hΨd.trans (hT Ψ).symm) X
  subst Ψd
  obtain ⟨Φ, hΦfin, hΦ⟩ := exists_tendsto_complexUnitaryFiniteSchwartz Ψ
  have hΦd : Tendsto (fun j => T (Φ j)) atTop (𝓝 (T Ψ)) := T.continuous.continuousAt.tendsto.comp hΦ
  obtain ⟨τ, σ, τd, σd, _, _, hf⟩ := complexLocalEqualFiniteSquareChambers D D₁ d ds hds e U B hB f hAdj
  choose F hF hg hgTilt hPlus hMinus using fun j : ℕ => hf (Φ j) (T (Φ j)) (hT _) (hΦfin j)
  let P := complexEqualNormalizedSquareTrace D₁ D.groupHaar d ds es 1 U.val V.val
  let Q := complexEqualNormalizedSquareTrace D₁ D.groupHaar d.inv
    (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
    (equalDoublePhase d ds es)⁻¹ Ud.val Vd.val
  have hP (j : ℕ) (z s : ℂ) (hz : τ < z.re) (hs : σ < s.re) :
      F j (z, s) = P (Φ j) z s := by
    simpa only [P, complexEqualNormalizedSquareTrace, one_mul] using hPlus j z s hz hs
  have hQ (j : ℕ) (z s : ℂ) (hz : τd < (-z).re) (hs : σd < s.re) :
      F j (z, 1 - s) = Q (T (Φ j)) (-z) s := hMinus j z s hz hs
  obtain ⟨α, β, hp⟩ := exists_complexEqualNormalizedSquareTrace_bound D₁ D.groupHaar d 1
    ds es U V ds es 1
  obtain ⟨αd, βd, hq⟩ := exists_complexEqualNormalizedSquareTrace_bound D₁ D.groupHaar d.inv (-1)
    (dualData ds) (dualData es) Ud Vd (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)
    (equalDoublePhase d ds es)⁻¹
  let primalShift := max τ α
  let primalSpectral := max σ β
  let dualShift := max τd αd
  let dualSpectral := max σd βd
  have hLines : ∀ R a b : ℝ, 0 ≤ R → a ≤ b → ∃ l u K L : ℝ, l < a ∧ b < u ∧ 0 ≤ L ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
        ∀ v s : ℂ, |v.re| ≤ R → s.re = l ∨ s.re = u →
          ‖F i (v + s, s) - F j (v + s, s)‖ ≤ ε * Real.exp (K * |s.im| + L * |v.im|) := by
    intro R a b hR _
    let l := min a (min (1 - dualSpectral) (-dualShift - R)) - 1
    let u := max b (max primalSpectral (primalShift + R)) + 1
    have hl : l < a := by
      dsimp only [l]
      linarith [min_le_left a (min (1 - dualSpectral) (-dualShift - R))]
    have hu : b < u := by
      dsimp only [u]
      linarith [le_max_left b (max primalSpectral (primalShift + R))]
    have hlu : primalShift < u - R := by
      dsimp only [u]
      linarith [(le_max_right primalSpectral (primalShift + R)).trans (le_max_right b _)]
    have hsu : primalSpectral < u := by
      dsimp only [u]
      linarith [(le_max_left primalSpectral (primalShift + R)).trans (le_max_right b _)]
    have hll : dualShift < -R - l := by
      dsimp only [l]
      linarith [(min_le_right a _).trans (min_le_right (1 - dualSpectral) (-dualShift - R))]
    have hsl : dualSpectral < 1 - l := by
      dsimp only [l]
      linarith [(min_le_right a _).trans (min_le_left (1 - dualSpectral) (-dualShift - R))]
    obtain ⟨Kp, Lp, pp, _, hLp, hpp, hpp₀, hbp⟩ := hp (u - R) (u + R) u
      ((le_max_right τ α).trans_lt hlu) (by linarith) ((le_max_right σ β).trans_lt hsu)
    obtain ⟨Km, Lm, pm, _, hLm, hpm, hpm₀, hbm⟩ := hq (-R - l) (R - l) (1 - l)
      ((le_max_right τd αd).trans_lt hll) (by linarith) ((le_max_right σd βd).trans_lt hsl)
    refine ⟨l, u, max (Kp + Lp) (Km + Lm), max Lp Lm, hl, hu, hLp.trans (le_max_left _ _), ?_⟩
    intro ε hε
    obtain ⟨Np, hNp⟩ := eventually_weight_sub hΦ hpp hpp₀ hε
    obtain ⟨Nm, hNm⟩ := eventually_weight_sub hΦd hpm hpm₀ hε
    refine ⟨max Np Nm, fun i j hi hj v s hv hs => ?_⟩
    obtain ⟨hvl, hvu⟩ := abs_le.mp hv
    rcases hs with hs | hs
    · let z := v + s
      let t := 1 - s
      have hzr₁ : -R - l ≤ (-z).re := by
        simp only [z, Complex.neg_re, Complex.add_re, hs]
        linarith
      have hzr₂ : (-z).re ≤ R - l := by
        simp only [z, Complex.neg_re, Complex.add_re, hs]
        linarith
      have htr : t.re = 1 - l := by simp only [t, Complex.sub_re, Complex.one_re, hs]
      have hzτ : τd < (-z).re := ((le_max_left _ _).trans_lt hll).trans_le hzr₁
      have htσ : σd < t.re := htr ▸ (le_max_left _ _).trans_lt hsl
      have ht : 1 - t = s := sub_sub_cancel 1 s
      have hti : |t.im| = |s.im| := by
        simp only [t, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      have hzi : |(-z).im| ≤ |v.im| + |s.im| := by
        simp only [z, Complex.neg_im, abs_neg, Complex.add_im]
        exact abs_add_le _ _
      change ‖F i (z, s) - F j (z, s)‖ ≤ _
      rw [← ht, hQ i z t hzτ htσ, hQ j z t hzτ htσ]
      rw [ht]
      exact (hbm (T (Φ i)) (T (Φ j)) (-z) t hzr₁ hzr₂ htr).trans
        (tilt_exponential_bound hε.le (hNm i j ((le_max_right _ _).trans hi) ((le_max_right _ _).trans hj))
          hLm (le_max_right _ _) (le_max_right _ _) hti hzi)
    · let z := v + s
      have hzr₁ : u - R ≤ z.re := by simp only [z, Complex.add_re, hs]; linarith
      have hzr₂ : z.re ≤ u + R := by simp only [z, Complex.add_re, hs]; linarith
      have hzτ : τ < z.re := ((le_max_left _ _).trans_lt hlu).trans_le hzr₁
      have hsσ : σ < s.re := hs ▸ (le_max_left _ _).trans_lt hsu
      have hzi : |z.im| ≤ |v.im| + |s.im| := by
        simp only [z, Complex.add_im]
        exact abs_add_le _ _
      change ‖F i (z, s) - F j (z, s)‖ ≤ _
      rw [hP i z s hzτ hsσ, hP j z s hzτ hsσ]
      exact (hbp (Φ i) (Φ j) z s hzr₁ hzr₂ hs).trans
        (tilt_exponential_bound hε.le (hNp i j ((le_max_left _ _).trans hi) ((le_max_left _ _).trans hj))
          hLp (le_max_left _ _) (le_max_left _ _) rfl hzi)
  obtain ⟨A, hA, hCurve, hGrowth⟩ := Langlands.Analysis.affineStripExtension F hF hg hgTilt hLines
  have hlim (p : ℂ × ℂ) : Tendsto (fun j => F j p) atTop (𝓝 (A p)) :=
    hA.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ p)
  refine ⟨A, hCurve, hGrowth, ⟨primalShift, primalSpectral, fun z s hz hs => ?_⟩, ⟨dualShift, dualSpectral, fun z s hz hs => ?_⟩⟩
  · obtain ⟨_, _, p, _, _, hpcont, hp₀, hb⟩ := hp z.re z.re s.re ((le_max_right _ _).trans_lt hz)
      le_rfl ((le_max_right _ _).trans_lt hs)
    have hlimP := tendsto_of_trace_bound hΦ hpcont hp₀ (fun Φ₁ Φ₂ => hb Φ₁ Φ₂ z s le_rfl le_rfl rfl)
    have h := tendsto_nhds_unique (hlim (z, s)) (hlimP.congr fun j =>
      (hP j z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)).symm)
    simpa only [P, complexEqualNormalizedSquareTrace, one_mul] using h
  · obtain ⟨_, _, p, _, _, hpcont, hp₀, hb⟩ := hq (-z).re (-z).re s.re ((le_max_right _ _).trans_lt hz)
      le_rfl ((le_max_right _ _).trans_lt hs)
    have hlimQ := tendsto_of_trace_bound hΦd hpcont hp₀ (fun Φ₁ Φ₂ => hb Φ₁ Φ₂ (-z) s le_rfl le_rfl rfl)
    exact tendsto_nhds_unique (hlim (z, 1 - s)) (hlimQ.congr fun j =>
      (hQ j z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)).symm)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
