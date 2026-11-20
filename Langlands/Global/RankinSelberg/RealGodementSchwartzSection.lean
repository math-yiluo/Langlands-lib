import Langlands.Global.RankinSelberg.RealGodementSchwartzMajorant
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Smoothness of the real Godement section for Schwartz tests -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Filter MeasureTheory Set
open scoped ContDiff Manifold Matrix.Norms.Operator NNReal SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

universe u

section ParametricIntegral

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {A : Type*} [MeasurableSpace A] {μ : Measure A} {s : Set V}

private theorem contDiffOn_integral_nat (hs : IsOpen s) (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : V → A → E),
      (∀ a, ContDiff ℝ ∞ (F · a)) →
      (∀ k x, x ∈ s → AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (F · a) x) μ) →
      (∀ k x, x ∈ s → ∃ T ∈ 𝓝 x, T ⊆ s ∧ ∃ b : A → ℝ, Integrable b μ ∧
        ∀ y ∈ T, ∀ a, ‖iteratedFDeriv ℝ k (F · a) y‖ ≤ b a) →
      ContDiffOn ℝ n (fun x => ∫ a, F x a ∂μ) s := by
  have hDerivative (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : V → A → E) (hF : ∀ a, ContDiff ℝ ∞ (F · a))
      (hMeas : ∀ k x, x ∈ s → AEStronglyMeasurable (fun a => iteratedFDeriv ℝ k (F · a) x) μ)
      (hBound : ∀ k x, x ∈ s → ∃ T ∈ 𝓝 x, T ⊆ s ∧ ∃ b : A → ℝ, Integrable b μ ∧
        ∀ y ∈ T, ∀ a, ‖iteratedFDeriv ℝ k (F · a) y‖ ≤ b a)
      (x : V) (hx : x ∈ s) : HasFDerivAt (fun y => ∫ a, F y a ∂μ)
        (∫ a, fderiv ℝ (F · a) x ∂μ) x := by
    obtain ⟨T₀, hT₀, _, b₀, hb₀, hB₀⟩ := hBound 0 x hx
    obtain ⟨T₁, hT₁, _, b₁, hb₁, hB₁⟩ := hBound 1 x hx
    have hm (y : V) (hy : y ∈ s) : AEStronglyMeasurable (F y) μ := by
      let v : Fin 0 → V := fun _ => 0
      simpa only [iteratedFDeriv_zero_apply] using
        (continuous_eval_const v).comp_aestronglyMeasurable (hMeas 0 y hy)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le hT₁
      (Filter.Eventually.mono (hs.mem_nhds hx) fun y hy => hm y hy)
      (hb₀.mono' (hm x hx) (ae_of_all _ fun a => by
        simpa only [norm_iteratedFDeriv_zero] using hB₀ x (mem_of_mem_nhds hT₀) a))
      ?_ (ae_of_all _ fun a y hy => by
        simpa only [norm_iteratedFDeriv_one] using hB₁ y hy a) hb₁
      (ae_of_all _ fun a y _ => ((hF a).differentiable (by simp) y).hasFDerivAt)
    let v : Fin 0 → V := fun _ => 0
    have hm₁ := (continuousMultilinearCurryRightEquiv' ℝ 0 V E).continuous.comp_aestronglyMeasurable
      (hMeas 1 x hx)
    refine ((continuous_eval_const v).comp_aestronglyMeasurable hm₁).congr
      (ae_of_all _ fun a => ?_)
    change (continuousMultilinearCurryRightEquiv' ℝ 0 V E)
      (iteratedFDeriv ℝ (0 + 1) (fun y => F y a) x) v = fderiv ℝ (fun y => F y a) x
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply,
      iteratedFDeriv_zero_apply]
  induction n with
  | zero =>
    intro E _ _ _ F hF hMeas hBound
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hDerivative E F hF hMeas hBound x hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro E _ _ _ F hF hMeas hBound
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun x hx => (hDerivative E F hF hMeas hBound x hx).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    let D (x : V) (a : A) := fderiv ℝ (F · a) x
    have hD : ContDiffOn ℝ n (fun x => ∫ a, D x a ∂μ) s := by
      refine ih _ D (fun a => (hF a).fderiv_right (by simp)) ?_ ?_
      · intro k x hx
        refine ((continuousMultilinearCurryRightEquiv' ℝ k V E).continuous.comp_aestronglyMeasurable
          (hMeas (k + 1) x hx)).congr (ae_of_all _ fun a => ?_)
        change (continuousMultilinearCurryRightEquiv' ℝ k V E)
          (iteratedFDeriv ℝ (k + 1) (fun y => F y a) x) =
            iteratedFDeriv ℝ k (fderiv ℝ (fun y => F y a)) x
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
      · intro k x hx
        obtain ⟨T, hT, hTs, b, hb, hB⟩ := hBound (k + 1) x hx
        refine ⟨T, hT, hTs, b, hb, fun y hy a => ?_⟩
        change ‖iteratedFDeriv ℝ k (fderiv ℝ (fun z => F z a)) y‖ ≤ b a
        rw [norm_iteratedFDeriv_fderiv]
        exact hB y hy a
    exact hD.congr fun x hx => (hDerivative E F hF hMeas hBound x hx).fderiv

end ParametricIntegral

open GramFormula PartialJacquet

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ

private theorem norm_rowsLinear_le (h : M) : ‖rowsLinear h‖ ≤ ‖h‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h) fun y => ?_
  have hrows : ‖lastRows y‖ ≤ ‖y‖ := by
    rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
    exact NNReal.coe_le_coe.mpr (Finset.sup_le fun i _ => by
      exact Finset.le_sup (f := fun j : Fin (m + 1) => ∑ l, ‖y j l‖₊)
        (Finset.mem_univ i.succ))
  exact (Matrix.linfty_opNorm_mul h (lastRows y)).trans
    (mul_le_mul_of_nonneg_left hrows (norm_nonneg h))

private theorem contMDiff_schwartzInnerIntegral (μ : Measure G) [μ.IsHaarMeasure]
    (Φ : 𝓢(X, ℂ)) {η : G → ℂ} (hη : Continuous η)
    (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hN : ∀ h : G, ‖η h‖ ≤ A * (|h.val.det| ^ m * (1 + ‖h.val‖) ^ N)) :
    ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ (innerIntegral μ Φ η) := by
  let F (y : Y) (h : G) : ℂ := η h * Φ (rowsLinear h.val y)
  have hf (h : G) : ContDiff ℝ ∞ (fun y => Φ (rowsLinear h.val y)) :=
    Φ.smooth'.comp (rowsLinear h.val).contDiff
  have hF (h : G) : ContDiff ℝ ∞ (F · h) := (hf h).const_smul (η h)
  have hDerivative (k : ℕ) (y : Y) (h : G) :
      iteratedFDeriv ℝ k (F · h) y =
        η h • (iteratedFDeriv ℝ k Φ (rowsLinear h.val y)).compContinuousLinearMap
          (fun _ => rowsLinear h.val) := by
    change iteratedFDeriv ℝ k (fun x => η h • (Φ ∘ rowsLinear h.val) x) y = _
    have h' : ContDiffAt ℝ k ((Φ : X → ℂ) ∘ rowsLinear h.val) y :=
      ((hf h).of_le (by simp)).contDiffAt
    rw [iteratedFDeriv_const_smul_apply' h',
      (rowsLinear h.val).iteratedFDeriv_comp_right (f := (Φ : X → ℂ))
        Φ.smooth' y (by simp)]
  have hMeas (k : ℕ) (y : Y) :
      AEStronglyMeasurable (fun h : G => iteratedFDeriv ℝ k (F · h) y) μ := by
    simp only [hDerivative]
    let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin k => Y) (fun _ : Fin k => X) ℂ
    have hCLM : Continuous (fun h : G => C (fun _ => rowsLinear h.val)) :=
      C.coe_continuous.comp (continuous_pi fun _ => continuous_parameterOperator)
    have hΦ := Φ.smooth'.continuous_iteratedFDeriv (m := k) (by simp)
    exact (hη.smul (hCLM.clm_apply
      (hΦ.comp (continuous_parameterOperator.clm_apply continuous_const)))).aestronglyMeasurable
  let S : Set Y := {y | IsUnit y}
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix (F := ℝ) (N := m + 1)
  obtain ⟨L, hL⟩ := exists_integrable_matrixDecay μ
  have hBound (k : ℕ) (y : Y) (hy : y ∈ S) :
      ∃ Q ∈ 𝓝 y, Q ⊆ S ∧ ∃ b : G → ℝ, Integrable b μ ∧
        ∀ z ∈ Q, ∀ h : G, ‖iteratedFDeriv ℝ k (F · h) z‖ ≤ b h := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS y hy
    let Q := Metric.closedBall y (ε / 2)
    have hQ : Q ⊆ S := (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    let T := (Units.val : Langlands.GeneralLinear (m + 1) ℝ → Y) ⁻¹' Q
    have hT : IsCompact T := isCompact_val_preimage (isCompact_closedBall _ _) hQ
    obtain ⟨B, hB, hΦ⟩ := exists_uniform_schwartz_decay hT Φ (N + k + L) k
    refine ⟨Q, mem_of_superset (Metric.ball_mem_nhds y (half_pos hε)) Metric.ball_subset_closedBall,
      hQ, fun h => (A * B) * (|h.val.det| ^ m * ((1 + ‖h.val‖) ^ L)⁻¹),
      hL.const_mul _, fun z hz h => ?_⟩
    obtain ⟨g, rfl⟩ := hQ hz
    have hOp : ‖rowsLinear h.val‖ ≤ 1 + ‖h.val‖ :=
      (norm_rowsLinear_le h.val).trans (le_add_of_nonneg_left zero_le_one)
    have hBase : 1 + ‖h.val‖ ≠ 0 := by positivity
    have hD := hΦ g hz h
    change ‖iteratedFDeriv ℝ k Φ (rowsLinear h.val g.val)‖ ≤ _ at hD
    rw [hDerivative]
    calc
      _ ≤ ‖η h‖ * (‖iteratedFDeriv ℝ k Φ (rowsLinear h.val g.val)‖ * ‖rowsLinear h.val‖ ^ k) := by
        refine (ContinuousMultilinearMap.opNorm_smul_le (η h) _).trans
          (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le
            (iteratedFDeriv ℝ k Φ (rowsLinear h.val g.val)) (fun _ => rowsLinear h.val)
      _ ≤ (A * (|h.val.det| ^ m * (1 + ‖h.val‖) ^ N)) *
          ((B * ((1 + ‖h.val‖) ^ (N + k + L))⁻¹) * (1 + ‖h.val‖) ^ k) := by
        refine mul_le_mul (hN h) ?_ (by positivity) (by positivity)
        exact mul_le_mul hD (pow_le_pow_left₀ (norm_nonneg _) hOp k) (by positivity) (by positivity)
      _ = _ := by
        simp only [pow_add, _root_.mul_inv_rev]
        field_simp
  refine contMDiff_of_contDiffOn (ψ := fun y : Y => ∫ h, F y h ∂μ) ?_ (fun _ => rfl)
  exact contDiffOn_infty.2 fun n =>
    contDiffOn_integral_nat hS n ℂ F hF (fun k y _ => hMeas k y) hBound

/-- On the lower Haar right half-plane, the real Godement integral of any Schwartz test
defines a smooth vector of the upper position principal series. -/
def RealGodementSchwartzSectionStatement : Prop :=
  ∀ (m : ℕ) (μ : Measure (Langlands.GeneralLinear m ℝ)) [μ.IsHaarMeasure]
    (c : RealCharacterData) (ds : List RealBlock) (f : Langlands.GeneralLinear m ℝ → ℂ),
    f ∈ principalSeries ℝ m (realPositionCharacter ds) →
    (∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) →
    ∀ Φ : 𝓢(Matrix (Fin m) (Fin (m + 1)) ℝ, ℂ),
      sectionValue μ c f Φ ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))

theorem realGodementSchwartzSection : RealGodementSchwartzSectionStatement := by
  intro m μ _ c ds f hf hc Φ
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let η (h : Langlands.GeneralLinear m ℝ) : ℂ :=
    f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h
  have hη : Continuous η := (hf.1.continuous.comp continuous_inv).mul
    (contMDiff_determinantWeight c _).continuous
  obtain ⟨N, A, hA, hN⟩ := exists_weightedLower_bound c ds hf hc
  have hBound : ∀ h, ‖η h‖ ≤ A * (|h.val.det| ^ m * (1 + ‖h.val‖) ^ N) := by
    simpa only [η, norm_mul] using hN
  refine ⟨?_, sectionValue_covariant μ c ds hf Φ⟩
  have hPair := (contMDiff_determinantWeight (n := m + 1) c ((m : ℂ) / 2)).prodMk
    (contMDiff_schwartzInnerIntegral μ Φ hη N A hA hBound)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hPair
  have hMul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_fst.mul contDiff_snd
  exact hMul.comp_contMDiff hPair

end Langlands.Global.RankinSelbergGlobal.RealGodement
