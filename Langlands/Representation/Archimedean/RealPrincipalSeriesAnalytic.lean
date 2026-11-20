import Langlands.Analysis.CompactMapAnalytic
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Analytic compact-picture orbits of the real Frobenius functions -/

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open RealJacquetFrobenius

universe uV

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "K" => unitaryCompact ℝ n

private theorem exists_analyticIwasawa :
    ∃ Ψ : Mat → Mat, AnalyticAt ℝ Ψ 1 ∧ Ψ 1 = 0 ∧
      ∀ᶠ A in 𝓝 1, iwMap 1 (Ψ A) = A := by
  have hb : (1 : Mat).IsUpperTriangular := Matrix.blockTriangular_one
  let D : Mat ≃L[ℝ] Mat := iwDerivEquiv hb isUnit_one
  have hd : HasFDerivAt (iwMap (1 : Mat)) (D : Mat →L[ℝ] Mat) 0 := by
    rw [show (D : Mat →L[ℝ] Mat) = iwDeriv 1 from iwDerivEquiv_coe hb isUnit_one]
    exact hasFDerivAt_iwMap 1
  have ha : AnalyticAt ℝ (iwMap (1 : Mat)) 0 := by
    have hU : AnalyticAt ℝ (fun A : Mat => 1 + upperPart A) 0 :=
      analyticAt_const.add (upperPart.analyticAt (0 : Mat))
    have hE : AnalyticAt ℝ (fun A : Mat => NormedSpace.exp (skewPart A)) 0 :=
      (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp (skewPart.analyticAt (0 : Mat))
    exact hU.mul hE
  have hs : HasStrictFDerivAt (iwMap (1 : Mat)) (D : Mat →L[ℝ] Mat) 0 := by
    rw [← hd.fderiv]
    exact ha.hasStrictFDerivAt
  have hzero : iwMap (1 : Mat) 0 = 1 := by simp [iwMap]
  let φ := hs.toOpenPartialHomeomorph (iwMap (1 : Mat))
  have hφ : (φ : Mat → Mat) = iwMap 1 := hs.toOpenPartialHomeomorph_coe
  have hφa : AnalyticAt ℝ (φ : Mat → Mat) 0 := hφ.symm ▸ ha
  have hφd : fderiv ℝ (φ : Mat → Mat) 0 = D := hφ.symm ▸ hd.fderiv
  have hinv := φ.analyticAt_symm' hs.mem_toOpenPartialHomeomorph_source hφa hφd
  have hpoint := hs.localInverse_apply_image
  have hevent := hs.eventually_right_inverse
  rw [hφ, hzero] at hinv
  rw [hzero] at hpoint hevent
  exact ⟨φ.symm, hinv, hpoint, hevent⟩

private theorem analyticAt_charFun_one (t : ℂ) (e : Fin 2) :
    AnalyticAt ℝ (charFun e t) 1 := by
  have h₁ : (1 : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (by norm_num : (0 : ℝ) < 1)
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ t) 1 :=
    analyticAt_id.cpow analyticAt_const h₁
  have hreal : AnalyticAt ℝ (fun x : ℝ => (x : ℂ) ^ t) 1 := by
    have h : AnalyticAt ℝ (fun z : ℂ => z ^ t) (Complex.ofRealCLM 1) := by
      simpa using hpow.restrictScalars (𝕜 := ℝ)
    exact h.comp (Complex.ofRealCLM.analyticAt 1)
  apply hreal.congr
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hx' : 0 < x := hx
  simp [charFun, abs_of_pos hx', div_self hx'.ne']

private theorem analyticAt_diagChar_one (a : Fin n → ℂ) (e : Fin n → Fin 2) :
    AnalyticAt ℝ (diagChar a e) 1 := by
  unfold diagChar
  apply Finset.analyticAt_fun_prod
  intro j _
  have h : AnalyticAt ℝ (charFun (e j) (a j)) (entryCLM j j (1 : Mat)) := by
    simpa only [entryCLM_apply, Matrix.one_apply_eq] using analyticAt_charFun_one (a j) (e j)
  exact h.comp ((entryCLM j j).analyticAt (1 : Mat))

private def compactMatrix : C(K, Mat) :=
  ⟨fun k => ((k : GL) : Mat), Units.continuous_val.comp continuous_subtype_val⟩

private def compactMatrixInv : C(K, Mat) :=
  ⟨fun k => (((k : GL)⁻¹ : GL) : Mat),
    Units.continuous_val.comp (continuous_inv.comp continuous_subtype_val)⟩

private def conjugates (A : Mat) : C(K, Mat) :=
  compactMatrix * ContinuousMap.const K A * compactMatrixInv

private theorem analyticAt_conjugates : AnalyticAt ℝ (conjugates (n := n)) 1 :=
  (analyticAt_const.mul
    ((ContinuousLinearMap.const ℝ K : Mat →L[ℝ] C(K, Mat)).analyticAt 1)).mul analyticAt_const

private theorem conjugates_one : conjugates (1 : Mat) = ContinuousMap.const K 1 := by
  apply ContinuousMap.ext
  intro k
  change ((k : GL) : Mat) * 1 * (((k : GL)⁻¹ : GL) : Mat) = (1 : Mat)
  rw [mul_one, ← Units.val_mul, mul_inv_cancel]
  rfl

private def compactEntry (ij : Fin n × Fin n) : C(K, Mat) →L[ℝ] C(K, ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℝ K (Complex.ofRealCLM.comp (entryCLM ij.1 ij.2))

/-- Evaluate a polynomial in the matrix entries pointwise on the compact group. -/
def compactPolyEval (P : MvPolynomial (Fin n × Fin n) ℂ) (A : C(K, Mat)) : C(K, ℂ) :=
  MvPolynomial.eval₂ (algebraMap ℂ C(K, ℂ)) (fun ij => compactEntry ij A) P

private theorem compactPolyEval_apply (P : MvPolynomial (Fin n × Fin n) ℂ)
    (A : C(K, Mat)) (k : K) : compactPolyEval P A k = polyEval P (A k) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [compactPolyEval, polyEval]
  | add p q hp hq =>
    simp [compactPolyEval, polyEval] at hp hq ⊢
    rw [hp, hq]
  | mul_X p ij hp =>
    simp [compactPolyEval, polyEval, compactEntry] at hp
    simp [compactPolyEval, polyEval, compactEntry, entryCLM_apply, hp]

private theorem analyticAt_compactPolyEval (P : MvPolynomial (Fin n × Fin n) ℂ) (A : C(K, Mat)) :
    AnalyticAt ℝ (compactPolyEval P) A := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : compactPolyEval (MvPolynomial.C c) = fun _ : C(K, Mat) =>
        ContinuousMap.const K c := by
      funext M
      simp [compactPolyEval]
      rfl
    rw [h]
    exact analyticAt_const
  | add p q hp hq =>
    have h : compactPolyEval (p + q) = fun M => compactPolyEval p M + compactPolyEval q M := by
      funext M
      simp [compactPolyEval]
    rw [h]
    exact hp.add hq
  | mul_X p ij hp =>
    have h : compactPolyEval (p * MvPolynomial.X ij) =
        fun M => compactPolyEval p M * compactEntry ij M := by
      funext M
      simp [compactPolyEval]
    rw [h]
    exact hp.mul ((compactEntry ij).analyticAt A)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V} {ℓ : V →ₗ[ℂ] ℂ}
  {a : Fin n → ℂ} {e : Fin n → Fin 2}

/-- Near the identity matrix, the translated compact profile of a Frobenius function is
represented by an analytic germ for the supremum norm. -/
theorem exists_analyticAt_compactOrbit_frobFun
    (hsign : ∀ (j : Fin n) (v : V), ℓ (ρ (signReflection n j) v) = (-1) ^ (e j).val * ℓ v)
    (v : V) {P : MvPolynomial (Fin n × Fin n) ℂ}
    (hP : ∀ k : Matrix.unitaryGroup (Fin n) ℝ, ℓ (ρ k v) = polyEval P (k : Mat)) :
    ∃ T : Mat → C(K, ℂ), AnalyticAt ℝ T 1 ∧
      ∀ᶠ A in 𝓝 (1 : Mat), ∀ g : GL, (g : Mat) = A →
        ∀ k : K, T A k = frobFun ρ ℓ a e v ((k : GL) * g) := by
  obtain ⟨Ψ, hΨ, hΨ0, hΨe⟩ := exists_analyticIwasawa (n := n)
  let b : Mat → Mat := fun A => 1 + upperPart (Ψ A)
  let q : Mat → Mat := fun A => NormedSpace.exp (skewPart (Ψ A))
  have hb : AnalyticAt ℝ b 1 := analyticAt_const.add ((upperPart.analyticAt (Ψ 1)).comp hΨ)
  have hb1 : b 1 = 1 := by simp [b, hΨ0]
  have hχb : AnalyticAt ℝ (diagChar a e) (b 1) := by
    rw [hb1]
    exact analyticAt_diagChar_one a e
  have hχ : AnalyticAt ℝ (fun A => diagChar a e (b A)) 1 := hχb.comp hb
  have hq : AnalyticAt ℝ q 1 :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp ((skewPart.analyticAt (Ψ 1)).comp hΨ)
  obtain ⟨χK, hχK, hχeval⟩ := Langlands.Analysis.exists_analyticAt_pointwise hχ K
  obtain ⟨qK, hqK, hqeval⟩ := Langlands.Analysis.exists_analyticAt_pointwise hq K
  have hχc : AnalyticAt ℝ (fun A => χK (conjugates A)) 1 :=
    (conjugates_one.symm ▸ hχK : AnalyticAt ℝ χK (conjugates 1)).comp analyticAt_conjugates
  have hqc : AnalyticAt ℝ (fun A => qK (conjugates A) * compactMatrix) 1 :=
    ((conjugates_one.symm ▸ hqK : AnalyticAt ℝ qK (conjugates 1)).comp
      analyticAt_conjugates).mul analyticAt_const
  let T : Mat → C(K, ℂ) := fun A => χK (conjugates A) *
    compactPolyEval P (qK (conjugates A) * compactMatrix)
  refine ⟨T, hχc.mul ((analyticAt_compactPolyEval P _).comp hqc), ?_⟩
  have hc : Tendsto (conjugates (n := n)) (𝓝 1) (𝓝 (ContinuousMap.const K 1)) := by
    rw [← conjugates_one]
    exact analyticAt_conjugates.continuousAt
  have hDecomp : ∀ᶠ u in 𝓝 (ContinuousMap.const K (1 : Mat)), ∀ k : K,
      b (u k) * q (u k) = u k := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hΨe
    filter_upwards [Metric.ball_mem_nhds (ContinuousMap.const K (1 : Mat)) hr] with u hu k
    exact hball (Metric.mem_ball.mpr ((ContinuousMap.dist_apply_le_dist k).trans_lt hu))
  filter_upwards [hc.eventually hχeval, hc.eventually hqeval, hc.eventually hDecomp]
    with A hAχ hAq hAb g hg k
  have hbtri : (b (conjugates A k)).IsUpperTriangular :=
    Matrix.blockTriangular_one.add (upperPart_isUpperTriangular _)
  have hqmem : q (conjugates A k) * compactMatrix k ∈ Matrix.unitaryGroup (Fin n) ℝ :=
    Submonoid.mul_mem _ (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewPart_mem _)) k.2
  have hfactor : (((k : GL) * g : GL) : Mat) =
      b (conjugates A k) * (q (conjugates A k) * compactMatrix k) := by
    rw [← mul_assoc, hAb k]
    change (((k : GL) * g : GL) : Mat) =
      (((k : GL) : Mat) * A * (((k : GL)⁻¹ : GL) : Mat)) * ((k : GL) : Mat)
    rw [← hg, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, mul_assoc _ _ (k : GL),
      inv_mul_cancel, mul_one]
  change χK (conjugates A) k * compactPolyEval P (qK (conjugates A) * compactMatrix) k = _
  rw [frobFun_eq hsign hbtri hqmem hfactor v, hP, compactPolyEval_apply,
    ContinuousMap.mul_apply, hAχ k, hAq k]

end Langlands.Archimedean.RealPrincipalSeriesHilbert
