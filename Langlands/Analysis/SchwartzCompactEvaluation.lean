import Langlands.Analysis.CompactParameterSmoothness
import Langlands.Analysis.MixedParameterDerivatives
import Langlands.Analysis.SchwartzCompactFamilies
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Smooth scalar evaluations of compactly supported Schwartz families -/

noncomputable section

open Filter Set
open scoped ContDiff NNReal SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SchwartzCompactFamilies

universe u v

variable {P : Type u} {E : Type v}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complex submodule of Schwartz tests vanishing off a specified set. -/
def supportedSchwartz (S : Set E) : Submodule ℂ 𝓢(E, ℂ) where
  carrier := {Φ | ∀ x ∉ S, Φ x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hΦ hΨ x hx => by
    change _ + _ = (0 : ℂ)
    rw [hΦ x hx, hΨ x hx, add_zero]
  smul_mem' := fun c _ hΦ x hx => by
    change c • _ = (0 : ℂ)
    rw [hΦ x hx, smul_zero]

/-- One spatial derivative of a supported Schwartz function, restricted to its support set. -/
def derivativeCoordinate (S : Set E) (n : ℕ) :
    supportedSchwartz S →ₗ[ℂ] C(S, E [×n]→L[ℝ] ℂ) where
  toFun Φ := ⟨fun x => iteratedFDeriv ℝ n Φ.val x.val,
    ((Φ.val.smooth n).continuous_iteratedFDeriv le_rfl).comp continuous_subtype_val⟩
  map_add' Φ Ψ := by
    ext1 x
    change iteratedFDeriv ℝ n (⇑Φ.val + ⇑Ψ.val) x.val = _
    exact iteratedFDeriv_add_apply (Φ.val.smooth n).contDiffAt (Ψ.val.smooth n).contDiffAt
  map_smul' c Φ := by
    ext1 x
    let L : ℂ →L[ℝ] ℂ := (c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ
    have hSmooth : ContDiffAt ℝ ∞ (⇑Φ.val : E → ℂ) x.val := Φ.val.smooth'.contDiffAt
    change iteratedFDeriv ℝ n (L ∘ ⇑Φ.val) x.val = c • iteratedFDeriv ℝ n Φ.val x.val
    rw [L.iteratedFDeriv_comp_left hSmooth (by simp)]
    rfl

private theorem exists_continuous_factor {V Z : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] (J : V →ₗ[ℂ] Z) (L : V →ₗ[ℂ] ℂ)
    {C : ℝ} (hC : ∀ f, ‖L f‖ ≤ C * ‖J f‖) : ∃ T : Z →L[ℂ] ℂ, ∀ f, T (J f) = L f := by
  have hker : J.ker ≤ L.ker := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply norm_eq_zero.mp (le_antisymm _ (norm_nonneg _))
    simpa only [hf, norm_zero, mul_zero] using hC f
  let T₀ := J.ker.liftQ L hker ∘ₗ J.quotKerEquivRange.symm.toLinearMap
  have hT₀ (f : V) : T₀ (J.rangeRestrict f) = L f := by
    change J.ker.liftQ L hker (J.quotKerEquivRange.symm ⟨J f, ⟨f, rfl⟩⟩) = L f
    rw [J.quotKerEquivRange_symm_apply_image]
    rfl
  have hNorm (y : J.range) : ‖T₀ y‖ ≤ C * ‖y‖ := by
    obtain ⟨f, hf⟩ := y.property
    have he : J.rangeRestrict f = y := Subtype.ext hf
    rw [← he, hT₀]
    exact hC f
  obtain ⟨T, hT, _⟩ := exists_extension_norm_eq J.range (T₀.mkContinuous C hNorm)
  exact ⟨T, fun f => (hT (J.rangeRestrict f)).trans (hT₀ f)⟩

private theorem seminorm_le_compactCoordinates {S : Set E} (hS : IsCompact S)
    [CompactSpace S] (I : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : supportedSchwartz S,
      I.sup (schwartzSeminormFamily ℝ E ℂ) Φ.val ≤ C *
        ‖(fun i : I => derivativeCoordinate S i.val.2 Φ)‖ := by
  obtain ⟨R₀, hR₀⟩ := hS.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (id : E → E) S)
  let R := max 1 R₀
  let k := I.sup Prod.fst
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos := zero_le_one.trans hR
  refine ⟨R ^ k, pow_nonneg hRpos _, fun Φ => ?_⟩
  let A := fun i : I => derivativeCoordinate S i.val.2 Φ
  apply Seminorm.finset_sup_apply_le (mul_nonneg (pow_nonneg hRpos _) (norm_nonneg _))
  intro i hi
  apply SchwartzMap.seminorm_le_bound ℝ i.1 i.2 _ (mul_nonneg (pow_nonneg hRpos _) (norm_nonneg _))
  intro x
  by_cases hx : x ∈ S
  · have hxR : ‖x‖ ≤ R := (hR₀ x hx).trans (le_max_right _ _)
    have hX : ‖x‖ ^ i.1 ≤ R ^ k :=
      (pow_le_pow_left₀ (norm_nonneg _) hxR _).trans (pow_le_pow_right₀ hR (Finset.le_sup hi))
    have hD : ‖iteratedFDeriv ℝ i.2 Φ.val x‖ ≤ ‖A‖ :=
      ((A ⟨i, hi⟩).norm_coe_le_norm ⟨x, hx⟩).trans (norm_le_pi_norm A ⟨i, hi⟩)
    exact mul_le_mul hX hD (norm_nonneg _) (pow_nonneg hRpos _)
  · have hZero : (⇑Φ.val : E → ℂ) =ᶠ[𝓝 x] (fun _ : E => (0 : ℂ)) := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact Φ.property y hy
    rw [(hZero.iteratedFDeriv ℝ i.2).eq_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero, mul_zero]
    positivity

/-- A bounded evaluation on compactly supported Schwartz tests factors through a
finite family of continuous spatial derivative coordinates. -/
theorem exists_compactJet_factor {S : Set E} (hS : IsCompact S) [CompactSpace S]
    (L : supportedSchwartz S →ₗ[ℂ] ℂ) (q : Seminorm ℝ 𝓢(E, ℂ)) (hq : Continuous q)
    (hB : ∀ f : supportedSchwartz S, ‖L f‖ ≤ q f.val) :
    ∃ (I : Finset (ℕ × ℕ)) (T : ((i : I) → C(S, E [×i.val.2]→L[ℝ] ℂ)) →L[ℂ] ℂ),
      ∀ f : supportedSchwartz S, T (fun i => derivativeCoordinate S i.val.2 f) = L f := by
  obtain ⟨I, A, _, hA⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ E ℂ) q hq
  let Y := (i : I) → C(S, E [×i.val.2]→L[ℝ] ℂ)
  let J : supportedSchwartz S →ₗ[ℂ] Y := LinearMap.pi fun i => derivativeCoordinate S i.val.2
  obtain ⟨C, _, hBound⟩ := seminorm_le_compactCoordinates hS I
  have hJ (f : supportedSchwartz S) : ‖L f‖ ≤ (A : ℝ) * C * ‖J f‖ := by
    calc
      _ ≤ q f.val := hB f
      _ ≤ (A : ℝ) * I.sup (schwartzSeminormFamily ℝ E ℂ) f.val := hA _
      _ ≤ (A : ℝ) * (C * ‖J f‖) := mul_le_mul_of_nonneg_left (hBound f) A.coe_nonneg
      _ = _ := (mul_assoc _ _ _).symm
  obtain ⟨T, hT⟩ := exists_continuous_factor (Z := Y) J L (C := (A : ℝ) * C) hJ
  exact ⟨I, T, hT⟩

private theorem fderiv_iteratedFDeriv_slice {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (p : P) (a : P) (x : E) (v : Fin n → E) :
    fderiv ℝ (fun q => iteratedFDeriv ℝ n (fun y => F (q, y)) x v) p a =
      iteratedFDeriv ℝ n (fun y => fderiv ℝ (fun q => F (q, y)) p a) x v := by
  let F' (y : E) := fderiv ℝ (fun q => F (q, y)) p a
  have hF' : ContDiff ℝ ∞ F' := by
    have hEq : F' = fun y => fderiv ℝ F (p, y) (a, 0) := by
      funext y
      exact Langlands.Analysis.fderiv_fst_slice_apply (hF.differentiable (by simp) (p, y)) a
    rw [hEq]
    exact ((hF.fderiv_right (m := ∞) (by simp)).comp
      (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  induction n generalizing x with
  | zero => simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
      have hn : (n : ℕ∞ω) < ∞ := ENat.natCast_lt_of_coe_top_le_withTop le_rfl n
      let H (z : P × E) := iteratedFDeriv ℝ n (fun y => F (z.1, y)) z.2 (Fin.tail v)
      have hH : ContDiff ℝ ∞ H :=
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℂ (Fin.tail v)).contDiff.comp
          (contDiff_iteratedFDeriv_slice hF n)
      have hEq : (fun q => iteratedFDeriv ℝ (n + 1) (fun y => F (q, y)) x v) =
          fun q => fderiv ℝ (fun y => H (q, y)) x (v 0) := by
        funext q
        have hSmooth : ContDiff ℝ ∞ (fun y : E => F (q, y)) :=
          hF.comp (contDiff_const.prodMk contDiff_id)
        exact (hSmooth.differentiable_iteratedFDeriv hn x).iteratedFDeriv_succ_apply_left'
      rw [hEq, Langlands.Analysis.fderiv_fst_snd_comm isOpen_univ isOpen_univ hH.contDiffOn
        (mem_univ p) (mem_univ x) a (v 0)]
      have hInner :
          (fun y => fderiv ℝ (fun q => H (q, y)) p a) =
            fun y => iteratedFDeriv ℝ n F' y (Fin.tail v) := funext fun y => ih y (Fin.tail v)
      rw [hInner]
      exact ((hF'.differentiable_iteratedFDeriv hn x).iteratedFDeriv_succ_apply_left').symm

/-- Smooth joint test families with support in a fixed compact set have smooth scalar
values under any linear form bounded by a continuous Schwartz seminorm. -/
def SchwartzCompactEvaluationStatement : Prop :=
  ∀ (P : Type u) (E : Type v) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set E), IsCompact S →
    ∀ (L : supportedSchwartz S →ₗ[ℂ] ℂ) (q : Seminorm ℝ 𝓢(E, ℂ)), Continuous q →
      (∀ f : supportedSchwartz S, ‖L f‖ ≤ q f.val) →
    ∀ (U : Set P), IsOpen U → ∀ (Φ : P → supportedSchwartz S) (F : P × E → ℂ),
      (∀ p ∈ U, ∀ x, (Φ p).val x = F (p, x)) → ContDiff ℝ ∞ F →
      ContDiffOn ℝ ∞ (fun p => L (Φ p)) U ∧
      ∀ p ∈ U, ∀ (a : P) (Ψ : supportedSchwartz S),
        (∀ x, Ψ.val x = fderiv ℝ (fun q => F (q, x)) p a) →
        fderiv ℝ (fun q => L (Φ q)) p a = L Ψ

theorem schwartzCompactEvaluation : SchwartzCompactEvaluationStatement.{u, v} := by
  intro P E _ _ _ _ S hS L q hq hB U hU Φ F hΦ hF
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨I, T, hT⟩ := exists_compactJet_factor hS L q hq hB
  let Y := (i : I) → C(S, E [×i.val.2]→L[ℝ] ℂ)
  let J : supportedSchwartz S →ₗ[ℂ] Y := LinearMap.pi fun i => derivativeCoordinate S i.val.2
  have hDiff : ContDiffOn ℝ ∞ (fun p => J (Φ p)) U := by
    apply contDiffOn_pi.2
    intro i
    let j : C(S, E) := ⟨Subtype.val, continuous_subtype_val⟩
    have hDiffF := contDiff_iteratedFDeriv_slice hF i.val.2
    apply Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint j hU isOpen_univ
      (fun _ => mem_univ _) hDiffF.contDiffOn
    intro p hp x
    change iteratedFDeriv ℝ i.val.2 (Φ p).val x.val =
      iteratedFDeriv ℝ i.val.2 (fun y => F (p, y)) x.val
    have heq : (⇑(Φ p).val : E → ℂ) = fun y => F (p, y) := funext (hΦ p hp)
    rw [heq]
  have hEq : (T.restrictScalars ℝ) ∘ (fun p => J (Φ p)) = fun p => L (Φ p) :=
    funext fun p => hT (Φ p)
  refine ⟨hEq ▸ (T.restrictScalars ℝ).contDiff.comp_contDiffOn hDiff, ?_⟩
  intro p hp a Ψ hΨ
  have hDiffAt := (hDiff.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hJet : fderiv ℝ (fun q => J (Φ q)) p a = J Ψ := by
    ext1 i
    ext1 x
    ext1 v
    let ev₀ : Y →L[ℝ] C(S, E [×i.val.2]→L[ℝ] ℂ) := ContinuousLinearMap.proj i
    let ev₁ := (ContinuousMap.evalCLM (R := ℝ) x).comp ev₀
    let ev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i.val.2 => E) ℂ v).comp ev₁
    have hEv := congrArg (fun L : P →L[ℝ] ℂ => L a)
      (ev.hasFDerivAt.comp p hDiffAt.hasFDerivAt).fderiv
    change ev (fderiv ℝ (fun q => J (Φ q)) p a) = ev (J Ψ)
    change fderiv ℝ (fun q => ev (J (Φ q))) p a = ev (fderiv ℝ (fun q => J (Φ q)) p a) at hEv
    rw [← hEv]
    have hNear : (fun q => ev (J (Φ q))) =ᶠ[𝓝 p]
        fun q => iteratedFDeriv ℝ i.val.2 (fun y => F (q, y)) x.val v := by
      filter_upwards [hU.mem_nhds hp] with q hq
      change iteratedFDeriv ℝ i.val.2 (Φ q).val x.val v = _
      have heq : (⇑(Φ q).val : E → ℂ) = fun y => F (q, y) := funext (hΦ q hq)
      rw [heq]
    rw [hNear.fderiv_eq, fderiv_iteratedFDeriv_slice hF]
    have heq : (⇑Ψ.val : E → ℂ) = fun y => fderiv ℝ (fun q => F (q, y)) p a := funext hΨ
    rw [← heq]
    rfl
  rw [← hEq, ((T.restrictScalars ℝ).hasFDerivAt.comp p hDiffAt.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply, hJet]
  exact hT Ψ

end Langlands.Analysis.SchwartzCompactFamilies
