import Langlands.Global.RankinSelberg.RealGodementSchwartzMajorant
import Langlands.Global.RankinSelberg.RealGodementOpenCellConvergence

/-! # Joint absolute convergence for general Schwartz Godement tests -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  exact Units.isOpenEmbedding_val.locallyCompactSpace
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

variable {m : ℕ}

local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ

private def innerKernel (c : RealCharacterData) (f : G → ℂ) (Φ : X → ℂ) (q : H) (h : G) : ℂ :=
  f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h * Φ (rowPoint h.val q)

private theorem continuous_innerKernel (c : RealCharacterData) {f : G → ℂ} (hf : Continuous f)
    {Φ : X → ℂ} (hΦ : Continuous Φ) : Continuous (fun p : H × G => innerKernel c f Φ p.1 p.2) := by
  have hRows : Continuous (fun q : H => lastRows q.val) :=
    continuous_matrix fun i j => Units.continuous_val.matrix_elem i.succ j
  have hPoint : Continuous (fun p : H × G => rowPoint p.2.val p.1) :=
    (Units.continuous_val.comp continuous_snd).matrix_mul (hRows.comp continuous_fst)
  have hWeight : Continuous (determinantWeight c (((m : ℂ) + 1) / 2) : G → ℂ) :=
    (contMDiff_determinantWeight c _).continuous
  exact (((hf.comp continuous_snd.inv).mul (hWeight.comp continuous_snd)).mul (hΦ.comp hPoint))

private theorem integrable_innerKernel (μ : Measure G) [μ.IsHaarMeasure] (c : RealCharacterData)
    (ds : List RealBlock) {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) (Φ : 𝓢(X, ℂ)) (q : H) :
    Integrable (innerKernel c f Φ q) μ := by
  obtain ⟨b, hb, hBound⟩ := realGodementSchwartzMajorant m μ c ds f hf hc Φ {q} isCompact_singleton
  have hC : Continuous (innerKernel c f Φ q) :=
    (continuous_innerKernel c hf.1.continuous Φ.continuous).comp (continuous_const.prodMk continuous_id)
  exact hb.mono' hC.aestronglyMeasurable (ae_of_all _ fun h => by
    simpa only [innerKernel, norm_mul] using hBound q (mem_singleton q) h)

private theorem continuous_absoluteSectionValue (μ : Measure G) [μ.IsHaarMeasure] (c : RealCharacterData)
    (ds : List RealBlock) {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) (Φ : 𝓢(X, ℂ)) :
    Continuous (absoluteSectionValue μ c f Φ) := by
  let K := innerKernel c f (Φ : X → ℂ)
  have hC : Continuous (fun p : H × G => K p.1 p.2) := continuous_innerKernel c hf.1.continuous Φ.continuous
  change Continuous (fun q : H => ‖determinantWeight c ((m : ℂ) / 2) q‖ * ∫ h, ‖K q h‖ ∂μ)
  refine (contMDiff_determinantWeight c ((m : ℂ) / 2)).continuous.norm.mul ?_
  refine continuous_iff_continuousAt.mpr fun q => ?_
  obtain ⟨T, hT, hTg⟩ := exists_compact_mem_nhds q
  obtain ⟨b, hb, hBound⟩ := realGodementSchwartzMajorant m μ c ds f hf hc Φ T hT
  have hNear : ∀ᶠ x in 𝓝 q, x ∈ T := hTg
  refine continuousAt_of_dominated (bound := b)
    (Eventually.of_forall fun x => ((hC.comp (continuous_const.prodMk continuous_id)).norm).aestronglyMeasurable)
    (hNear.mono fun x hx => ae_of_all _ fun h => ?_) hb (ae_of_all _ fun h => ?_)
  · simpa only [norm_norm, K, innerKernel, norm_mul] using hBound x hx h
  · exact ((hC.comp (continuous_id.prodMk continuous_const)).norm).continuousAt

/-- For any Schwartz test the expanded Godement kernel is jointly integrable in
the strict chamber when the leading exponent also satisfies the lower Haar bound. -/
def RealGodementSchwartzJointStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (c : RealCharacterData) (ds : List RealBlock)
    (f : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    f ∈ principalSeries ℝ (t + 1) (realPositionCharacter ds) →
    IsStrictlyDominant (realPositionExponent (.character c :: ds)) (t + 1) →
    (∀ i : Fin (t + 1), ((t + 1 : ℕ) : ℝ) + normExponent (realPositionExponent ds) (t + 1) i ≤
      c.exponent.re + (((t + 1 : ℕ) : ℝ) + 1) / 2) →
    ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)) (g : Langlands.GeneralLinear (t + 2) ℝ),
      Integrable (godementOpenCellKernel a c f Φ g) ((upperStepHaar (t + 1) a).prod D.groupHaar) ∧
      additiveJacquetIntegral a (sectionValue D.groupHaar c f Φ) g =
        godementColumnValue D a Φ (additiveJacquetIntegral a f) c (weylLong (t + 2) ℝ * g)

theorem realGodementSchwartzJoint : RealGodementSchwartzJointStatement := by
  intro t D a c ds f hf hDom hc Φ g
  let m := t + 1
  let Lower := Langlands.GeneralLinear m ℝ
  let Upper := Langlands.GeneralLinear (m + 1) ℝ
  let U := GeneralLinear.upperUnipotent (m + 1) ℝ
  let μ := D.groupHaar
  let η := upperStepHaar (t + 1) a
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite μ := inferInstance
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let : SigmaFinite η := upperStepHaar_sigmaFinite (t + 1) a
  let e := realPositionExponent (.character c :: ds)
  let F := fun q : Upper => (absoluteSectionValue μ c f Φ q : ℂ)
  let b := fun d => (‖principalSeriesCharacter ℝ (m + 1) (realPositionCharacter (.character c :: ds)) d‖ : ℂ)
  let k : U → Upper := fun u => weylLong (m + 1) ℝ * u.val * g
  have hF : Continuous F := Complex.continuous_ofReal.comp
    (continuous_absoluteSectionValue μ c ds hf hc Φ)
  have hCov (d : Fin (m + 1) → ℝˣ) (u : U) (q : Upper) :
      F (Iwasawa.diagonalUnits d * u.val * q) = b d * F q := by
    simpa only [F, b, Complex.ofReal_mul] using
      congrArg Complex.ofReal (absoluteSectionValue_covariant μ c ds hf Φ d u q)
  have hChar (d : Fin (m + 1) → ℝˣ) : ‖b d‖ = ∏ i : Fin (m + 1), |(d i : ℝ)| ^ normExponent e (m + 1) i := by
    change ‖(‖principalSeriesCharacter ℝ _ _ d‖ : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_principalSeriesCharacter (RealStrictCharacterLanglandsQuotient.isSignedPower _) _ _
  have hσ (j : ℕ) (hj : j < t + 1) : normExponent e (m + 1) (j + 1) - normExponent e (m + 1) j < -1 := by
    have h := hDom j hj
    change (e (j + 1)).re < (e j).re at h
    unfold normExponent
    push_cast
    linarith
  have hOuter := realGodementOpenCellConvergence (t + 1) a F b (normExponent e (m + 1)) hF hCov hChar hσ g
  let d : U → ℂ := fun u => determinantWeight c ((m : ℂ) / 2) (k u)
  let A := innerKernel c f (Φ : Matrix (Fin m) (Fin (m + 1)) ℝ → ℂ)
  let ψ : U → ℂ := fun u => (standardCharacter (realScaledCharacter a) (t + 1) u : ℂ)
  have hForm (p : U × Lower) : godementOpenCellKernel a c f Φ g p = d p.1 * A (k p.1) p.2 * ψ p.1 := by
    have hm : (m : ℂ) = (t : ℂ) + 1 := Nat.cast_succ t
    unfold godementOpenCellKernel d A innerKernel k ψ
    rw [hm]
  have hNormψ (u : U) : ‖ψ u‖ = 1 := norm_standardCharacter _ _ _
  have hk : Continuous k := (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hd : Continuous d := (contMDiff_determinantWeight c ((m : ℂ) / 2)).continuous.comp hk
  have hA : Continuous (fun p : Upper × Lower => A p.1 p.2) := continuous_innerKernel c hf.1.continuous Φ.continuous
  have hψ : Continuous ψ := Units.continuous_val.comp
    (standardCharacterContinuous (realScaledCharacter a) (t + 1)).continuous
  have hKernel : Continuous (godementOpenCellKernel a c f Φ g) := by
    rw [funext hForm]
    exact ((hd.comp continuous_fst).mul (hA.comp ((hk.comp continuous_fst).prodMk continuous_snd))).mul
      (hψ.comp continuous_fst)
  have hSlice (u : U) : Integrable (fun h : Lower => godementOpenCellKernel a c f Φ g (u, h)) μ := by
    simp only [hForm]
    exact ((integrable_innerKernel μ c ds hf hc Φ (k u)).const_mul (d u)).mul_const (ψ u)
  have hEval (u : U) : (∫ h : Lower, ‖godementOpenCellKernel a c f Φ g (u, h)‖ ∂μ) =
      ‖additiveJacquetKernel a F g u‖ := by
    simp only [hForm, norm_mul, hNormψ, mul_one, additiveJacquetKernel, norm_standardCharacter]
    change (∫ h : Lower, ‖d u‖ * ‖A (k u) h‖ ∂μ) = ‖(absoluteSectionValue μ c f Φ (k u) : ℂ)‖
    rw [integral_const_mul, Complex.norm_real, Real.norm_of_nonneg]
    · rfl
    · exact mul_nonneg (norm_nonneg _) (integral_nonneg fun h => norm_nonneg _)
  have hInt : Integrable (godementOpenCellKernel a c f Φ g) (η.prod μ) :=
    (integrable_prod_iff hKernel.aestronglyMeasurable).2
      ⟨ae_of_all _ hSlice, hOuter.norm.congr (ae_of_all _ fun u => (hEval u).symm)⟩
  exact ⟨hInt, (realGodementAdditiveJacquet t D a c f Φ g hInt).2.2⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
