import Langlands.Analysis.CompactManifoldFunctionFamily
import Langlands.Analysis.DixmierMalliavin.Line
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Factorization in one direction for compactly supported functionals -/

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.CompactFunctional

section Restriction

variable {H : Type*} [TopologicalSpace H]

/-- A continuous function read in the supremum norm on a compact subset. -/
def restrict (B : Compacts H) : C(H, ℂ) →ₗ[ℂ] C(B, ℂ) where
  toFun f := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_apply (B : Compacts H) (f : C(H, ℂ)) (y : B) :
    restrict B f y = f y.val := rfl

variable [Group H] [IsTopologicalGroup H]

/-- Positive left translation on the argument of a continuous function. -/
def shift (a : H) : C(H, ℂ) →ₗ[ℂ] C(H, ℂ) where
  toFun f := f.comp ⟨fun x => a * x, continuous_const.mul continuous_id⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shift_apply (a : H) (f : C(H, ℂ)) (y : H) : shift a f y = f (a * y) := rfl

@[simp] theorem shift_one (f : C(H, ℂ)) : shift (1 : H) f = f := by ext y; simp

theorem shift_shift (a b : H) (f : C(H, ℂ)) : shift b (shift a f) = shift (a * b) f := by
  ext y
  simp [mul_assoc]

end Restriction

/-- Extend a bounded linear functional that is given on the image of a linear restriction. -/
private theorem exists_extend_bounded {S Y : Type*} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (T : S →ₗ[ℂ] Y) (L : S →ₗ[ℂ] ℂ)
    (M : ℝ) (hM : 0 ≤ M) (h : ∀ f, ‖L f‖ ≤ M * ‖T f‖) :
    ∃ Λ : Y →L[ℂ] ℂ, ‖Λ‖ ≤ M ∧ ∀ f, Λ (T f) = L f := by
  have hker : LinearMap.ker T ≤ LinearMap.ker L := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    exact norm_le_zero_iff.mp (by simpa only [hf, norm_zero, mul_zero] using h f)
  let A := ((LinearMap.ker T).liftQ L hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hA (f : S) : A (T.rangeRestrict f) = L f := by
    have he : T.quotKerEquivRange ((LinearMap.ker T).mkQ f) = T.rangeRestrict f := Subtype.ext rfl
    change (LinearMap.ker T).liftQ L hker (T.quotKerEquivRange.symm (T.rangeRestrict f)) = L f
    rw [← he, LinearEquiv.symm_apply_apply]
    rfl
  have hbound (y : LinearMap.range T) : ‖A y‖ ≤ M * ‖y‖ := by
    obtain ⟨f, hf⟩ := y.property
    have he : T.rangeRestrict f = y := Subtype.ext hf
    rw [← he, hA]
    exact h f
  obtain ⟨Λ, hΛ, hnorm⟩ := exists_extension_norm_eq (LinearMap.range T) (A.mkContinuous M hbound)
  exact ⟨Λ, hnorm.le.trans (A.mkContinuous_norm_le hM hbound),
    fun f => (hΛ (T.rangeRestrict f)).trans (hA f)⟩

section SmoothFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [ChartedSpace E H]
  [LieGroup 𝓘(ℝ, E) ∞ H]

local notation "I" => 𝓘(ℝ, E)

/-- Restrict the translated function to a compact subset. -/
theorem contMDiff_restrict_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {B : Compacts H} {q : V → H} {f : C(H, ℂ)}
    (hq : ContMDiff 𝓘(ℝ, V) I ∞ q) (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) :
    ContDiff ℝ ∞ (fun t => restrict B (shift (q t) f)) := by
  let j : C(B, H) := ⟨Subtype.val, continuous_subtype_val⟩
  have hh : ContMDiff (𝓘(ℝ, V).prod I) 𝓘(ℝ, ℂ) ∞
      (fun p : V × H => f (q p.1 * p.2)) :=
    hf.comp ((hq.comp contMDiff_fst).mul contMDiff_snd)
  exact contMDiff_iff_contDiff.mp (contMDiff_compactFamily_of_joint j hh (fun _ _ => rfl))

end SmoothFamily

section IteratedDeriv

variable {U V : Type*} [NormedAddCommGroup U] [NormedAddCommGroup V]

theorem iteratedDeriv_real_clm [NormedSpace ℝ U] [NormedSpace ℝ V] (T : U →L[ℝ] V) {F : ℝ → U} (hF : ContDiff ℝ ∞ F)
    (p : ℕ) (t : ℝ) : iteratedDeriv p (fun s => T (F s)) t = T (iteratedDeriv p F t) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ p (T ∘ F) t (fun _ => 1) = _
  rw [T.iteratedFDeriv_comp_left hF.contDiffAt (n := ∞) (by exact_mod_cast le_top)]
  rfl

theorem iteratedDeriv_clm [NormedSpace ℂ U] [NormedSpace ℂ V] (T : U →L[ℂ] V)
    {F : ℝ → U} (hF : ContDiff ℝ ∞ F) (p : ℕ) (t : ℝ) :
    iteratedDeriv p (fun s => T (F s)) t = T (iteratedDeriv p F t) :=
  iteratedDeriv_real_clm (T.restrictScalars ℝ) hF p t

end IteratedDeriv

section Factorization

variable {H : Type*} [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

/-- Uniform bounds on derivatives along a one-parameter subgroup, in one compact norm
for all orders. The compact may depend on the initial compact and the subgroup direction. -/
def LineDerivativeBounds (S : Submodule ℂ C(H, ℂ)) (B : Compacts H) (q : ℝ → H) (ε : ℝ) : Prop :=
  ∃ (V : Compacts H) (M : ℕ → ℝ), (∀ p, 0 ≤ M p) ∧
    ∀ (f : C(H, ℂ)), f ∈ S → ∀ p t, t ∈ Icc 0 ε →
      ‖iteratedDeriv p (fun s => restrict B (shift (q s) f)) t‖ ≤ M p * ‖restrict V f‖

private theorem dirac_eq_of_scaled_bound {g k : ℝ → ℂ} {c M : ℕ → ℝ} {ε : ℝ}
    (hD : ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → (∀ p t, t ∈ Icc 0 ε → ‖iteratedDeriv p F t‖ ≤ M p) →
      F 0 = (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) + ∫ t, F t * k t)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) {b : ℝ} (hb : 0 < b)
    (hbound : ∀ p t, t ∈ Icc 0 ε → ‖iteratedDeriv p F t‖ ≤ M p * b) :
    F 0 = (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) + ∫ t, F t * k t := by
  let d : ℂ := (b⁻¹ : ℝ)
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hb.ne')
  have hdiff := hF.const_smul d
  have hiter (p : ℕ) (t : ℝ) : iteratedDeriv p (d • F) t = d * iteratedDeriv p F t := by
    exact iteratedDeriv_const_smul (hF.contDiffAt.of_le (by exact_mod_cast le_top)) d
  have heq := hD (d • F) hdiff (fun p t ht => by
    rw [hiter, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
    calc
      _ ≤ b⁻¹ * (M p * b) := mul_le_mul_of_nonneg_left (hbound p t ht) (inv_nonneg.mpr hb.le)
      _ = M p := by field_simp)
  simp only [Pi.smul_apply, smul_eq_mul, hiter, mul_assoc, integral_const_mul] at heq
  simp_rw [mul_left_comm (↑(c _) : ℂ) d, tsum_mul_left, ← mul_add] at heq
  exact mul_left_cancel₀ hd heq

/-- On a translation-stable solution space with compact derivative bounds, the
Dixmier–Malliavin identity decomposes a bounded compact functional in one direction. -/
theorem exists_directional_factorization
    (S : Submodule ℂ C(H, ℂ))
    (hshift : ∀ (a : H) (f : C(H, ℂ)), f ∈ S → shift a f ∈ S)
    (B : Compacts H) (L : C(B, ℂ) →L[ℂ] ℂ) (q : ℝ → H)
    (hq0 : q 0 = 1) (hqadd : ∀ s t, q (s + t) = q s * q t)
    (hsmooth : ∀ (f : C(H, ℂ)), f ∈ S → ContDiff ℝ ∞ (fun s => restrict B (shift (q s) f)))
    {ε : ℝ} (hε : 0 < ε) (hbound : LineDerivativeBounds S B q ε) :
    ∃ (V : Compacts H) (L₁ : C(V, ℂ) →L[ℂ] ℂ) (g k : ℝ → ℂ),
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc 0 ε ∧ tsupport k ⊆ Icc 0 ε ∧
      ∀ (f : C(H, ℂ)), f ∈ S →
        L (restrict B f) = (∫ t, g t * L₁ (restrict V (shift (q t) f))) +
          ∫ t, k t * L (restrict B (shift (q t) f)) := by
  obtain ⟨V, M, hM, hB⟩ := hbound
  let w (f : S) (t : ℝ) := restrict B (shift (q t) f.val)
  let M' (p : ℕ) := ‖L‖ * M p
  have hM' (p : ℕ) : 0 ≤ M' p := mul_nonneg (norm_nonneg _) (hM p)
  have hws (f : S) : ContDiff ℝ ∞ (w f) := hsmooth f.val f.property
  let F (f : S) (t : ℝ) := L (w f t)
  have hFs (f : S) : ContDiff ℝ ∞ (F f) := (L.restrictScalars ℝ).contDiff.comp (hws f)
  have hFbound (f : S) (p : ℕ) (t : ℝ) (ht : t ∈ Icc 0 ε) :
      ‖iteratedDeriv p (F f) t‖ ≤ M' p * ‖restrict V f.val‖ := by
    rw [show iteratedDeriv p (F f) t = L (iteratedDeriv p (w f) t) from
      iteratedDeriv_clm L (hws f) p t]
    dsimp only [M']
    rw [mul_assoc]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB f.val f.property p t ht) (norm_nonneg _))
  let T := (restrict V).comp S.subtype
  let Λ (p : ℕ) : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => iteratedDeriv p (F f) 0
      map_add' := fun f g => by
        have he : F (f + g) = F f + F g := by funext t; simp [F, w]
        simp only [he]
        exact iteratedDeriv_add ((hFs f).contDiffAt.of_le (by exact_mod_cast le_top))
          ((hFs g).contDiffAt.of_le (by exact_mod_cast le_top))
      map_smul' := fun a f => by
        have he : F (a • f) = a • F f := by funext t; simp [F, w]
        simp only [he, RingHom.id_apply]
        exact iteratedDeriv_const_smul ((hFs f).contDiffAt.of_le (by exact_mod_cast le_top)) a }
  choose D hDn hD using fun p => exists_extend_bounded T (Λ p) (M' p) (hM' p)
    (fun f => hFbound f p 0 ⟨le_rfl, hε.le⟩)
  obtain ⟨c, g, k, hgs, hks, hg, hk, hc, hDir⟩ :=
    DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add M' hε
  let L₁ : C(V, ℂ) →L[ℂ] ℂ := ∑' p, (c p : ℂ) • D p
  have hDsum : Summable (fun p => (c p : ℂ) • D p) := by
    apply Summable.of_norm_bounded hc
    intro p
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hDn p) (abs_nonneg _)
  refine ⟨V, L₁, g, k, hgs, hks, hg, hk, ?_⟩
  intro f hf
  let u : S := ⟨f, hf⟩
  let b := 1 + ‖restrict V f‖
  have hb : 0 < b := by positivity
  have hfb (p : ℕ) (t : ℝ) (ht : t ∈ Icc 0 ε) : ‖iteratedDeriv p (F u) t‖ ≤ M' p * b :=
    (hFbound u p t ht).trans (mul_le_mul_of_nonneg_left (by dsimp [b, u]; linarith) (hM' p))
  have h := dirac_eq_of_scaled_bound hDir (F u) (hFs u) hb hfb
  have hder (p : ℕ) (t : ℝ) : D p (restrict V (shift (q t) f)) = iteratedDeriv p (F u) t := by
    let v : S := ⟨shift (q t) f, hshift (q t) f hf⟩
    have hcomp : F v = fun s => F u (s + t) := by
      funext s
      change L (restrict B (shift (q s) (shift (q t) f))) = L (restrict B (shift (q (s + t)) f))
      rw [shift_shift, add_comm s t, hqadd]
    change D p (T v) = _
    rw [hD p v]
    change iteratedDeriv p (F v) 0 = _
    simp only [hcomp, iteratedDeriv_comp_add_const, zero_add]
  have hL₁ (t : ℝ) : L₁ (restrict V (shift (q t) f)) =
      ∑' p, (c p : ℂ) * iteratedDeriv p (F u) t := by
    let ev := ContinuousLinearMap.apply ℂ ℂ (restrict V (shift (q t) f))
    change ev L₁ = _
    rw [show ev L₁ = ∑' p, ev ((c p : ℂ) • D p) from ev.map_tsum hDsum]
    simp only [ev, map_smul, ContinuousLinearMap.apply_apply, smul_eq_mul, hder]
  let integrand (p : ℕ) (t : ℝ) := (c p : ℂ) * (iteratedDeriv p (F u) t * g t)
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hg
  have hi (p : ℕ) : Integrable (integrand p) :=
    (((hFs u).continuous_iteratedDeriv p (by exact_mod_cast le_top)).mul hgs.continuous
      |>.integrable_of_hasCompactSupport hgc.mul_left).const_mul _
  have hbint (p : ℕ) (t : ℝ) : ‖integrand p t‖ ≤ (|c p| * M' p * b) * ‖g t‖ := by
    by_cases ht : t ∈ Icc 0 ε
    · rw [show ‖integrand p t‖ = |c p| * ‖iteratedDeriv p (F u) t‖ * ‖g t‖ by
        simp only [integrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hfb p t ht) (abs_nonneg _)
    · have hz : g t = 0 := image_eq_zero_of_notMem_tsupport (fun ht' => ht (hg ht'))
      simp [integrand, hz]
  have hsum : Summable (fun p => ∫ t, ‖integrand p t‖) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
      (fun p => ?_) ((hc.mul_right b).mul_right (∫ t, ‖g t‖))
    rw [← integral_const_mul]
    exact integral_mono (hi p).norm ((hgs.continuous.integrable_of_hasCompactSupport hgc).norm.const_mul _)
      (hbint p)
  have hI : (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p (F u) t * g t) =
      ∫ t, g t * L₁ (restrict V (shift (q t) f)) := by
    simp_rw [← integral_const_mul]
    change (∑' p, ∫ t, integrand p t) = _
    rw [integral_tsum_of_summable_integral_norm hi hsum]
    congr 1
    funext t
    rw [hL₁, ← tsum_mul_left]
    exact tsum_congr fun p => by dsimp [integrand]; ring
  rw [hI] at h
  have h0 : F u 0 = L (restrict B f) := by simp [F, w, u, hq0]
  rw [h0] at h
  simpa only [F, w, u, mul_comm _ (k _)] using h

end Factorization

end Langlands.Analysis.CompactFunctional
