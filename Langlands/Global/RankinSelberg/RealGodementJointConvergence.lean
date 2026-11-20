import Langlands.Global.RankinSelberg.RealGodementOpenCellConvergence
import Langlands.Global.RankinSelberg.RealGodementRowCompletion
import Langlands.Representation.Archimedean.RealLeviLimit
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # A nonnegative majorant for the real Godement open-cell kernel -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet RealInducedStandardBound

private def positiveCharacter (e : ℝ) : RealCharacterData := RealJacquetFrobenius.charData 0 e

private theorem positiveCharacter_apply (e : ℝ) (x : ℝˣ) :
    ((positiveCharacter e).character x : ℂ) = ((|(x : ℝ)| : ℝ) : ℂ) ^ (e : ℂ) := by
  rw [(positiveCharacter e).character_eq]
  simp [positiveCharacter, RealJacquetFrobenius.charData]

private def positiveBlocks : List RealBlock → List RealBlock
  | [] => []
  | .character c :: ds => .character (positiveCharacter c.exponent.re) :: positiveBlocks ds
  | .induced d :: ds =>
      .character (positiveCharacter (realPositionExponent (.induced d :: ds) 0).re) ::
      .character (positiveCharacter (realPositionExponent (.induced d :: ds) 1).re) ::
      positiveBlocks ds

private theorem realPositionCharacter_positiveBlocks_apply :
    ∀ (es : List RealBlock) (j : ℕ) (x : ℝˣ), realPositionCharacter (positiveBlocks es) j x =
      absChar (fun i => (realPositionExponent es i).re) j x
  | [], _, _ => by simp [positiveBlocks, realPositionCharacter, realPositionExponent, absChar]
  | .character _ :: _, 0, _ => positiveCharacter_apply _ _
  | .character _ :: es, j + 1, x => realPositionCharacter_positiveBlocks_apply es j x
  | .induced _ :: _, 0, _ => positiveCharacter_apply _ _
  | .induced _ :: _, 1, _ => positiveCharacter_apply _ _
  | .induced _ :: es, j + 2, x => realPositionCharacter_positiveBlocks_apply es j x

private theorem realPositionCharacter_positiveBlocks (ds : List RealBlock) :
    realPositionCharacter (positiveBlocks ds) = absChar (fun j => (realPositionExponent ds j).re) :=
  funext fun j => funext (realPositionCharacter_positiveBlocks_apply ds j)

private theorem absPrincipalSeriesCharacter (n : ℕ) (ds : List RealBlock) (d : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (absChar (fun j => (realPositionExponent ds j).re)) d =
      (‖principalSeriesCharacter ℝ n (realPositionCharacter ds) d‖ : ℂ) := by
  rw [norm_principalSeriesCharacter (RealStrictCharacterLanglandsQuotient.isSignedPower ds)]
  simp only [principalSeriesCharacter, absChar, Complex.ofReal_prod, Module.finrank_self,
    pow_one, Real.norm_eq_abs]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Complex.ofReal_cpow (abs_nonneg _)]
  have h : (((|(d l : ℝ)| : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (d l).ne_zero
  rw [← Complex.cpow_add _ _ h]
  congr 1
  push_cast
  ring

private theorem exists_expFun_majorant {n : ℕ} (ds : List RealBlock)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n (realPositionCharacter ds)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      let F := expFun n (fun j => (realPositionExponent ds j).re) g
      F = (F.re : ℂ) ∧ 0 ≤ F.re ∧ ‖f g‖ ≤ C * F.re := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hf.1.continuous
  refine ⟨C, (norm_nonneg _).trans (hC 1 (unitaryCompact ℝ n).one_mem), fun g => ?_⟩
  let e := fun j => (realPositionExponent ds j).re
  obtain ⟨d, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  have h1 := expFun_mul n e 1 hk
  rw [one_mul, expFun_one] at h1
  change expFun n e (Iwasawa.diagonalUnits d * u.val * k) = _ ∧ _ ∧ _
  rw [(expFun_mem n e).2, h1, mul_one, absPrincipalSeriesCharacter, Complex.ofReal_re,
    hf.2, norm_mul]
  exact ⟨rfl, norm_nonneg _, by rw [mul_comm C]; exact mul_le_mul_of_nonneg_left (hC k hk) (norm_nonneg _)⟩

private theorem norm_realCharacter (c : RealCharacterData) (x : ℝˣ) :
    ‖(c.character x : ℂ)‖ = |(x : ℝ)| ^ c.exponent.re := by
  have hsign : ‖(((x : ℝ) / |(x : ℝ)| : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs, div_self (abs_ne_zero.mpr x.ne_zero)]
  rw [c.character_eq, norm_mul, norm_pow, hsign, one_pow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr x.ne_zero)]

private theorem determinantWeight_positive_eq {n : ℕ} (c : RealCharacterData) (s : ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    determinantWeight (positiveCharacter c.exponent.re) (s : ℂ) g =
      (‖determinantWeight c (s : ℂ) g‖ : ℂ) := by
  let x := determinant g
  change ((positiveCharacter c.exponent.re).character x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ) =
    (‖(c.character x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ (s : ℂ)‖ : ℂ)
  rw [positiveCharacter_apply, norm_mul, norm_realCharacter,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr x.ne_zero), Complex.ofReal_re,
    Complex.ofReal_mul, Complex.ofReal_cpow (abs_nonneg _), Complex.ofReal_cpow (abs_nonneg _)]

private theorem continuous_determinantWeight_realGodement {n : ℕ} (c : RealCharacterData) (z : ℂ) :
    Continuous (determinantWeight (n := n) c z : Langlands.GeneralLinear n ℝ → ℂ) := by
  have hval : Continuous (fun g : Langlands.GeneralLinear n ℝ => g.val.det) :=
    Units.continuous_val.matrix_det
  have hDet : Continuous (determinant : Langlands.GeneralLinear n ℝ → ℝˣ) := by
    refine Units.continuous_iff.mpr ⟨hval, ?_⟩
    simp only [← map_inv]
    change Continuous (fun g : Langlands.GeneralLinear n ℝ => (g⁻¹).val.det)
    exact hval.comp continuous_inv
  have hbase : Continuous (fun g : Langlands.GeneralLinear n ℝ => ((|g.val.det| : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hval.abs
  have hpow : Continuous (fun g : Langlands.GeneralLinear n ℝ => ((|g.val.det| : ℝ) : ℂ) ^ z) := by
    refine continuous_iff_continuousAt.mpr fun g => ?_
    have h : ContinuousAt (fun x : ℂ => x ^ z) ((|g.val.det| : ℝ) : ℂ) :=
      continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr
        (abs_pos.mpr (determinant g).ne_zero))
    exact ContinuousAt.comp (f := fun k : Langlands.GeneralLinear n ℝ => ((|k.val.det| : ℝ) : ℂ))
      h (hbase.continuousAt (x := g))
  exact (Units.continuous_val.comp (c.character.continuous.comp hDet)).mul hpow

variable {m : ℕ}

local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ

private theorem exists_smooth_fullRank_majorant {S : Set X}
    (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x) {Φ : X → ℂ}
    (hΦ : Continuous Φ) (hΦS : ∀ x ∉ S, Φ x = 0) :
    ∃ (T : Set X) (b : X → ℝ), IsCompact T ∧ (∀ x ∈ T, HasFullRowRank x) ∧
      ContDiff ℝ ∞ b ∧ (∀ x ∉ T, b x = 0) ∧ (∀ x, ‖Φ x‖ ≤ b x) := by
  obtain ⟨U, hU, hSU, hUR⟩ := hS.exists_isOpen_closure_subset
    (isOpen_fullRowRank.mem_nhdsSet.mpr hRank)
  obtain ⟨V, hV, hSV, hVC⟩ := exists_isOpen_superset_and_isCompact_closure hS
  obtain ⟨φ, hφ, hφ01, hφsupp, hφone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := ⊤) (hU.inter hV) hS.isClosed (subset_inter hSU hSV)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hΦ.continuousOn
  let M := max C 0
  refine ⟨closure (U ∩ V), fun x => M * φ x,
    hVC.of_isClosed_subset isClosed_closure (closure_mono inter_subset_right),
    fun x hx => hUR (closure_mono inter_subset_left hx), contDiff_const.mul hφ, ?_, ?_⟩
  · intro x hx
    have hzero : φ x = 0 := by
      by_contra h
      have hmem : x ∈ Function.support φ := h
      exact hx (subset_closure (hφsupp ▸ hmem))
    change M * φ x = 0
    rw [hzero, mul_zero]
  · intro x
    change ‖Φ x‖ ≤ M * φ x
    by_cases hx : x ∈ S
    · rw [(hφone x).mp hx, mul_one]
      exact (hC x hx).trans (le_max_left _ _)
    · rw [hΦS x hx, norm_zero]
      exact mul_nonneg (le_max_right _ _) (hφ01 (mem_range_self x)).1

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

/-- For compact full-row-rank tests, the expanded Godement kernel is jointly
absolutely integrable throughout the strictly dominant chamber. -/
def RealGodementJointConvergenceStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (c : RealCharacterData) (ds : List RealBlock)
    (f : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    f ∈ principalSeries ℝ (t + 1) (realPositionCharacter ds) →
    IsStrictlyDominant (realPositionExponent (.character c :: ds)) (t + 1) →
    ∀ (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S →
      (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)),
      (∀ x ∉ S, Φ x = 0) →
    ∀ g, Integrable (godementOpenCellKernel a c f Φ g) ((upperStepHaar (t + 1) a).prod D.groupHaar)

theorem realGodementJointConvergence : RealGodementJointConvergenceStatement := by
  intro t D a c ds f hf hDom S hS hRank Φ hΦS g
  let n := t + 1
  let G := Langlands.GeneralLinear n ℝ
  let H := Langlands.GeneralLinear (n + 1) ℝ
  let U := GeneralLinear.upperUnipotent (n + 1) ℝ
  let Y := Matrix (Fin n) (Fin (n + 1)) ℝ
  let μ := D.groupHaar
  let η := upperStepHaar (t + 1) a
  let : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℝ))
  let : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite μ := inferInstance
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let : SigmaFinite η := upperStepHaar_sigmaFinite (t + 1) a
  obtain ⟨T, b, hT, hTR, hbSmooth, hbT, hb⟩ := exists_smooth_fullRank_majorant hS hRank Φ.continuous hΦS
  obtain ⟨C, hC, hSpherical⟩ := exists_expFun_majorant ds hf
  let e := fun j => (realPositionExponent ds j).re
  let E := fun j => (realPositionExponent (.character c :: ds) j).re
  let F := expFun n e
  let cPositive := positiveCharacter c.exponent.re
  let Ψ := fun x : Y => (b x : ℂ)
  have hF : F ∈ principalSeries ℝ n (realPositionCharacter (positiveBlocks ds)) := by
    rw [realPositionCharacter_positiveBlocks]
    exact expFun_mem n e
  have hSection : sectionValue μ cPositive F Ψ ∈ principalSeries ℝ (n + 1) (absChar E) := by
    have hp := realGodementSection n μ cPositive (positiveBlocks ds) F hF T hT hTR Ψ
      (Complex.ofRealCLM.contDiff.comp hbSmooth) (fun x hx => by simp [Ψ, hbT x hx])
    change sectionValue μ cPositive F Ψ ∈ principalSeries ℝ (n + 1)
      (realPositionCharacter (positiveBlocks (.character c :: ds))) at hp
    rwa [realPositionCharacter_positiveBlocks] at hp
  have hOuterInt : Integrable (additiveJacquetKernel a (sectionValue μ cPositive F Ψ) g) η :=
    integrable_additiveJacquetKernel_of_mem_principalSeries a (RealLeviLimit.isSignedPower_absChar E)
      (fun j hj => by simpa only [E, Complex.ofReal_re] using hDom j hj) hSection g
  let s : ℝ := (n : ℝ) / 2
  let s' : ℝ := ((n : ℝ) + 1) / 2
  have hs : (s : ℂ) = (n : ℂ) / 2 := by simp [s]
  have hs' : (s' : ℂ) = ((n : ℂ) + 1) / 2 := by simp [s']
  let k := fun u : U => weylLong (n + 1) ℝ * u.val * g
  let point := fun p : U × G => rowPoint p.2.val (k p.1)
  let d := fun p : U × G => determinantWeight c ((n : ℂ) / 2) (k p.1)
  let d' := fun p : U × G => determinantWeight c (((n : ℂ) + 1) / 2) p.2
  have hRankCast : (n : ℂ) = (t : ℂ) + 1 := Nat.cast_succ t
  have hKernelFormula (p : U × G) : godementOpenCellKernel a c f Φ g p =
      d p * (f p.2⁻¹ * d' p * Φ (point p)) *
        (standardCharacter (realScaledCharacter a) (t + 1) p.1 : ℂ) := by
    unfold godementOpenCellKernel
    rw [← hRankCast]
  let major := fun p : U × G => ‖d p‖ * ((F p.2⁻¹).re * ‖d' p‖ * b (point p))
  have hNonneg (p : U × G) : 0 ≤ major p :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (hSpherical p.2⁻¹).2.1 (norm_nonneg _))
      ((norm_nonneg _).trans (hb (point p))))
  have hk : Continuous k := (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hValue : Continuous (Units.val : H → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
    Units.continuous_val
  have hRows : Continuous (fun k : H => lastRows k.val) :=
    continuous_matrix fun i j => hValue.matrix_elem i.succ j
  have hPoint : Continuous point :=
    (Units.continuous_val.comp continuous_snd).matrix_mul (hRows.comp (hk.comp continuous_fst))
  have hd : Continuous d := (continuous_determinantWeight_realGodement c _).comp (hk.comp continuous_fst)
  have hd' : Continuous d' := (continuous_determinantWeight_realGodement c _).comp continuous_snd
  have hMajor : Continuous major :=
    hd.norm.mul (((Complex.continuous_re.comp ((expFun_mem n e).1.continuous.comp
      continuous_snd.inv)).mul hd'.norm).mul (hbSmooth.continuous.comp hPoint))
  have hSlice (u : U) : Integrable (fun h : G => major (u, h)) μ := by
    let V := {h : G | ∃ x ∈ ({k u} : Set H), rowPoint h.val x ∈ T}
    have hV : IsCompact V := isCompact_support_preimage isCompact_singleton hT hTR
    refine (hMajor.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport ?_
    refine hV.of_isClosed_subset isClosed_closure (closure_minimal ?_ hV.isClosed)
    intro h hh
    by_contra hV'
    have hz : b (point (u, h)) = 0 := hbT _ (fun ht => hV' ⟨k u, mem_singleton _, ht⟩)
    apply hh
    change major (u, h) = 0
    simp only [major, hz, mul_zero]
  have hEval (u : U) : ((∫ h : G, major (u, h) ∂μ : ℝ) : ℂ) = sectionValue μ cPositive F Ψ (k u) := by
    calc
      _ = ∫ h : G, (major (u, h) : ℂ) ∂μ := integral_complex_ofReal.symm
      _ = _ := by
        rw [sectionValue, innerIntegral, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun h => ?_)
        change ((major (u, h) : ℝ) : ℂ) = determinantWeight cPositive ((n : ℂ) / 2) (k u) *
          (F h⁻¹ * determinantWeight cPositive (((n : ℂ) + 1) / 2) h * Ψ (point (u, h)))
        have hFh : F h⁻¹ = ((F h⁻¹).re : ℂ) := (hSpherical h⁻¹).1
        rw [← hs, ← hs', determinantWeight_positive_eq, determinantWeight_positive_eq, hFh]
        simp only [major, d, d', Ψ, Complex.ofReal_mul, hs, hs']
        rfl
  have hEqNorm (u : U) :
      (∫ h : G, ‖major (u, h)‖ ∂μ) = ‖additiveJacquetKernel a (sectionValue μ cPositive F Ψ) g u‖ := by
    have heq : (∫ h : G, ‖major (u, h)‖ ∂μ) = ∫ h : G, major (u, h) ∂μ :=
      integral_congr_ae (ae_of_all _ fun h => by
        change ‖major (u, h)‖ = major (u, h)
        rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg (u, h))])
    rw [heq, additiveJacquetKernel, norm_mul, norm_standardCharacter, mul_one,
      show weylLong (t + 1 + 1) ℝ * u.val * g = k u from rfl, ← hEval,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun h => hNonneg (u, h))]
  have hMajorInt : Integrable major (η.prod μ) :=
    (integrable_prod_iff hMajor.aestronglyMeasurable).2
      ⟨ae_of_all _ hSlice, hOuterInt.norm.congr (ae_of_all _ fun u => (hEqNorm u).symm)⟩
  have hPhase : Continuous (fun p : U × G => (standardCharacter (realScaledCharacter a) (t + 1) p.1 : ℂ)) :=
    (Units.continuous_val.comp (standardCharacterContinuous (realScaledCharacter a) (t + 1)).continuous).comp
      continuous_fst
  have hKernel : Continuous (godementOpenCellKernel a c f Φ g) := by
    rw [funext hKernelFormula]
    exact (hd.mul (((hf.1.continuous.comp continuous_snd.inv).mul hd').mul
      (Φ.continuous.comp hPoint))).mul hPhase
  refine Integrable.mono' (hMajorInt.const_mul C) hKernel.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  simp only [hKernelFormula, norm_mul, norm_standardCharacter, mul_one]
  calc
    _ ≤ ‖d p‖ * ((C * (F p.2⁻¹).re) * ‖d' p‖ * b (point p)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (hb _) (norm_nonneg _) ?_) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right (hSpherical p.2⁻¹).2.2 (norm_nonneg _)
      · exact mul_nonneg (mul_nonneg hC (hSpherical p.2⁻¹).2.1) (norm_nonneg _)
    _ = _ := by unfold major; ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
