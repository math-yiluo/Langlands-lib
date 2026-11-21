import Langlands.Analysis.HolomorphicLinearContinuation
import Langlands.Global.RankinSelberg.RealGodementSpectralColumn

/-! # Finite spectral descent with locally uniform right derivatives -/

noncomputable section

open Langlands.Archimedean Langlands.Analysis
open Filter Matrix Metric Set
open scoped Classical ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {r n k : ℕ} {J : Type*}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Y" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "P" => (Fin n → ℂ)
local notation "V" => (Fin k → ℂ)
local notation "Mat" => Matrix (Fin k) (Fin k) ℂ
local notation "I" => matrixModel ℝ (r + 1)
local notation "Dᵣ" => RealLocalWhittaker.iteratedRightDerivative r

private theorem contMDiff_const_smul {f : G → ℂ} (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (c : ℂ) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (c • f) :=
  ((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hf

private theorem iteratedRightDerivative_sum {l : Type*} (s : Finset l) (F : l → G → ℂ)
    (hF : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℂ) ∞ (F i)) (Xs : List Y) :
    Dᵣ Xs (∑ i ∈ s, F i) = ∑ i ∈ s, Dᵣ Xs (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, RealUniformWhittaker.iteratedRightDerivative_zero]
  | insert i s hi ih =>
    have hFi := hF i (Finset.mem_insert_self i s)
    have hFs (j : l) (hj : j ∈ s) := hF j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      RealUniformWhittaker.iteratedRightDerivative_add hFi (contMDiff_finsetSum' hFs), ih hFs]

private theorem uniformGrowth_sum {l : Type*} [Fintype l] {U : Set P}
    (F : l → P → G → ℂ) (a : P → l → ℂ) (B : l → ℝ)
    (hB : ∀ i, 0 ≤ B i) (ha : ∀ i q, q ∈ U → ‖a q i‖ ≤ B i)
    (N : l → ℕ)
    (hF : ∀ i (Xs : List Y), ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ U, ∀ g,
      ‖Dᵣ Xs (F i q) g‖ ≤ C * realMatrixHeight g ^ N i) :
    ∀ Xs : List Y, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ U, ∀ g,
      ‖∑ i, a q i * Dᵣ Xs (F i q) g‖ ≤ C * realMatrixHeight g ^ Finset.univ.sup N := by
  intro Xs
  choose C hC using fun i => hF i Xs
  refine ⟨∑ i, B i * C i, Finset.sum_nonneg (fun i _ => mul_nonneg (hB i) (hC i).1), fun q hq g => ?_⟩
  have hHeight : 1 ≤ realMatrixHeight g :=
    le_trans (by norm_num) (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos r) g)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  refine mul_le_mul (ha i q hq) ((hC i).2 q hq g |>.trans ?_) (norm_nonneg _) (hB i)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hHeight (Finset.le_sup (Finset.mem_univ i))) (hC i).1

private theorem frameExpansion (v : J → P → V) (hv : ∀ j i, Differentiable ℂ (fun q => v j q i))
    (b : Fin k → J) (q₀ : P) (hb : (Matrix.of fun i j => v (b i) q₀ j : Mat).det ≠ 0)
    (x : V) :
    ∃ a : P → V, (∀ i, DifferentiableAt ℂ (fun q => a q i) q₀) ∧
      ∀ᶠ q in 𝓝 q₀, x = ∑ i, a q i • v (b i) q := by
  let T (q : P) : Mat := Matrix.of fun i j => v (b j) q i
  have hT₀ : (T q₀).det ≠ 0 := by
    change ((Matrix.of fun i j => v (b i) q₀ j : Mat)ᵀ).det ≠ 0
    rwa [Matrix.det_transpose]
  have hT (i j : Fin k) : Differentiable ℂ (fun q => T q i j) := hv (b j) i
  have hd := Langlands.Analysis.differentiable_det hT
  let a (q : P) (i : Fin k) := (T q).cramer x i / (T q).det
  refine ⟨a, fun i => ?_, ?_⟩
  · have hn := Langlands.Analysis.differentiable_cramer hT
      (y := fun _ => x) (fun _ => differentiable_const _) i
    change DifferentiableAt ℂ (fun q => (T q).cramer x i / (T q).det) q₀
    simp only [div_eq_mul_inv]
    change DifferentiableAt ℂ ((fun q => (T q).cramer x i) * (fun q => (T q).det)⁻¹) q₀
    exact (hn q₀).mul ((hd q₀).inv hT₀)
  · have hNear : ∀ᶠ q in 𝓝 q₀, (T q).det ≠ 0 :=
      (isOpen_ne_fun hd.continuous continuous_const).mem_nhds hT₀
    filter_upwards [hNear] with q hq
    have he : a q = (T q).det⁻¹ • (T q).cramer x := by
      funext i
      simp only [a, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      exact mul_comm _ _
    have hx : T q *ᵥ a q = x := by
      rw [he, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hq, one_smul]
    funext j
    simpa only [Finset.sum_apply, Matrix.mulVec, dotProduct, T, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm] using (congrFun hx j).symm

/-- Entire compact generator coordinates and their smooth group-valued coefficients
descend to linear forms with holomorphic right derivatives and uniform local growth. -/
def RealGodementSpectralDescentStatement (r n k : ℕ) (J : Type*) : Prop :=
  ∀ (v : J → (Fin n → ℂ) → Fin k → ℂ)
    (F : J → (Fin n → ℂ) → Langlands.GeneralLinear (r + 1) ℝ → ℂ),
    (∀ j i, Differentiable ℂ (fun q => v j q i)) →
    (∀ q, ∃ b : Fin k → J, (Matrix.of fun i j => v (b i) q j :
      Matrix (Fin k) (Fin k) ℂ).det ≠ 0) →
    (∀ j q, ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (F j q)) →
    (∀ j (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) g, Differentiable ℂ
      (fun q => RealLocalWhittaker.iteratedRightDerivative r Xs (F j q) g)) →
    (∀ j, HasLocallyUniformDerivativeGrowth univ (F j)) →
    ∀ (S : Set (Fin n → ℂ)), IsOpen S → S.Nonempty →
    ∀ c₀ : (Fin n → ℂ) → Langlands.GeneralLinear (r + 1) ℝ → Fin k → ℂ,
      (∀ q ∈ S, ∀ j g, v j q ⬝ᵥ c₀ q g = F j q g) →
      ∃ L : (Fin n → ℂ) → (Fin k → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
        (∀ q j, L q (v j q) = F j q) ∧
        (∀ q ∈ S, ∀ x g, L q x g = x ⬝ᵥ c₀ q g) ∧
        ∀ x, (∀ q, ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (L q x)) ∧
          HasLocallyUniformDerivativeGrowth univ (fun q => L q x) ∧
          ∀ Xs g, Differentiable ℂ (fun q => RealLocalWhittaker.iteratedRightDerivative r Xs (L q x) g)

theorem realGodementSpectralDescent : RealGodementSpectralDescentStatement r n k J := by
  intro v F hv hb hFs hFd hFG S hS hNonempty c₀ hInit
  choose u hu using fun g : G =>
    holomorphicLinearContinuation v (fun j q => F j q g) hv (fun j => hFd j [] g)
      hb S hS hNonempty (fun q => c₀ q g) fun q hq j => hInit q hq j g
  let L (q : P) : V →ₗ[ℂ] (G → ℂ) := {
    toFun := fun x g => x ⬝ᵥ u g q
    map_add' := fun x y => funext fun g => add_dotProduct x y (u g q)
    map_smul' := fun c x => funext fun g => by
      change (c • x) ⬝ᵥ u g q = c * (x ⬝ᵥ u g q)
      rw [smul_dotProduct, smul_eq_mul] }
  have hL (q : P) (j : J) : L q (v j q) = F j q :=
    funext fun g => (hu g).2.1 q j
  refine ⟨L, hL, fun q hq x g => congrArg (dotProduct x) ((hu g).2.2 hq), fun x => ?_⟩
  have hLocal (q₀ : P) : ∃ δ : ℝ, 0 < δ ∧
      (∀ q ∈ ball q₀ δ, ContMDiff I 𝓘(ℝ, ℂ) ∞ (L q x)) ∧
      (∃ N : ℕ, ∀ Xs : List Y, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ ball q₀ δ, ∀ g,
        ‖Dᵣ Xs (L q x) g‖ ≤ C * realMatrixHeight g ^ N) ∧
      ∀ Xs g, DifferentiableAt ℂ (fun q => Dᵣ Xs (L q x) g) q₀ := by
    obtain ⟨b, hb₀⟩ := hb q₀
    obtain ⟨a, ha, he⟩ := frameExpansion v hv b q₀ hb₀ x
    choose ε hε N hN using fun i : Fin k => hFG (b i) q₀ (mem_univ q₀)
    have hNear : ∀ᶠ q in 𝓝 q₀, ∀ i, q ∈ ball q₀ (ε i) ∧ ‖a q i‖ < ‖a q₀ i‖ + 1 := by
      apply eventually_all.mpr
      intro i
      have hεNear : ∀ᶠ q in 𝓝 q₀, q ∈ ball q₀ (ε i) := ball_mem_nhds q₀ (hε i)
      exact hεNear.and ((ha i).continuousAt.norm.eventually_lt continuousAt_const (lt_add_one _))
    obtain ⟨δ, hδ, hBall⟩ := Metric.eventually_nhds_iff_ball.mp (he.and hNear)
    have hSum (q : P) (hq : q ∈ ball q₀ δ) : L q x = ∑ i, a q i • F (b i) q := by
      calc
        _ = L q (∑ i, a q i • v (b i) q) := congrArg (L q) (hBall q hq).1
        _ = _ := by simp only [map_sum, map_smul, hL]
    have hEach (q : P) (i : Fin k) : ContMDiff I 𝓘(ℝ, ℂ) ∞ (a q i • F (b i) q) :=
      contMDiff_const_smul (hFs (b i) q) (a q i)
    have hDer (Xs : List Y) (q : P) (hq : q ∈ ball q₀ δ) (g : G) :
        Dᵣ Xs (L q x) g = ∑ i, a q i * Dᵣ Xs (F (b i) q) g := by
      rw [hSum q hq, iteratedRightDerivative_sum _ _ (fun i _ => hEach q i)]
      simp only [RealUniformWhittaker.iteratedRightDerivative_smul (hFs _ _),
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨δ, hδ, fun q hq => hSum q hq ▸ contMDiff_finsetSum' (fun i _ => hEach q i),
      ⟨Finset.univ.sup N, ?_⟩, fun Xs g => ?_⟩
    · intro Xs
      obtain ⟨C, hC, h⟩ := uniformGrowth_sum (fun i => F (b i)) a (fun i => ‖a q₀ i‖ + 1)
        (fun i => by positivity) (fun i q hq => ((hBall q hq).2 i).2.le) N
        (fun i Ys => by
          obtain ⟨C, hC, h⟩ := hN i Ys
          exact ⟨C, hC, fun q hq => h q ((hBall q hq).2 i).1⟩) Xs
      exact ⟨C, hC, fun q hq g => hDer Xs q hq g ▸ h q hq g⟩
    · have hD : DifferentiableAt ℂ (fun q => ∑ i, a q i * Dᵣ Xs (F (b i) q) g) q₀ :=
        DifferentiableAt.fun_sum fun i _ => (ha i).mul (hFd (b i) Xs g).differentiableAt
      have hNear : ∀ᶠ q in 𝓝 q₀, q ∈ ball q₀ δ := ball_mem_nhds q₀ hδ
      exact hD.congr_of_eventuallyEq (hNear.mono fun q hq => hDer Xs q hq g)
  refine ⟨fun q => ?_, fun q _ => ?_, fun Xs g q => ?_⟩
  · obtain ⟨δ, hδ, hs, _⟩ := hLocal q
    exact hs q (mem_ball_self hδ)
  · obtain ⟨δ, hδ, _, hGrowth, _⟩ := hLocal q
    exact ⟨δ, hδ, hGrowth⟩
  · obtain ⟨_, _, _, _, hD⟩ := hLocal q
    exact hD Xs g

end Langlands.Global.RankinSelbergGlobal.RealGodement
