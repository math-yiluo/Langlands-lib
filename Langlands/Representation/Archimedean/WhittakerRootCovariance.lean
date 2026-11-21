import Langlands.Analysis.FixedSupportTestDerivative
import Langlands.Representation.Archimedean.WhittakerRootPhase

/-! # Infinitesimal covariance of smooth matrix distributions along upper roots -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace Langlands.HarmonicAnalysis Langlands.GeneralLinear
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

namespace Langlands.Archimedean

universe uF

variable {F : Type uF} [RCLike F] {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) F
local notation "D" => 𝓓(matrixUnitsOpen F n, ℂ)

/-- Left multiplication by a matrix unit as a real continuous linear equivalence. -/
def matrixLeftMulEquiv (u : Mˣ) : M ≃L[ℝ] M where
  toLinearEquiv :=
    { toFun := fun x => u.val * x
      invFun := fun x => u⁻¹.val * x
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc]
      map_add' := fun _ _ => mul_add _ _ _
      map_smul' := fun _ _ => mul_smul_comm _ _ _ }
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- Pull back a test by left multiplication `x ↦ u * x`. -/
def matrixLeftTranslateTest (u : Mˣ) : D →L[ℂ] D :=
  Analysis.testLinearPullback (matrixLeftMulEquiv u) (fun _ hx => (Units.isUnit u⁻¹).mul hx)

@[simp]
theorem matrixLeftTranslateTest_apply (u : Mˣ) (f : D) (x : M) :
    matrixLeftTranslateTest u f x = f (u.val * x) := rfl

/-- Evaluation of a smooth matrix distribution on a translated test
is differentiable along an actual upper-root line. -/
theorem hasDerivAt_upperRoot_distribution
    (T : D →L[ℂ] ℂ) (p : MatrixPositiveRoot n) (z : F) (f : D) :
    HasDerivAt
      (fun t : ℝ => T (matrixLeftTranslateTest (upperRootTransvection p (t • z)).val f))
      (T (matrixLeftTestDerivative (Matrix.single p.val.1 p.val.2 z) f)) 0 := by
  classical
  let U (t : ℝ) : Mˣ := (upperRootTransvection p (t • z)).val
  let X : M := Matrix.single p.val.1 p.val.2 z
  have hU (t : ℝ) : (U t).val = 1 + t • X := by
    change (upperRootTransvection p (t • z)).val.val = _
    rw [upperRootTransvection_val, Matrix.smul_single]
  have hUi (t : ℝ) : (U t)⁻¹.val = 1 + (-t) • X := by
    change 1 + Matrix.single p.val.1 p.val.2 (-(t • z)) = _
    rw [Matrix.smul_single, neg_smul]
  let A (q : ℝ × M) := (1 + (-q.1) • X) * q.2
  let K : Compacts M :=
    ⟨A '' (Icc (-1 : ℝ) 1 ×ˢ tsupport f),
      (isCompact_Icc.prod f.hasCompactSupport).image
        ((continuous_const.add (continuous_fst.neg.smul continuous_const)).mul continuous_snd)⟩
  have hK : (K : Set M) ⊆ matrixUnitsOpen F n := by
    rintro x ⟨⟨t, y⟩, ht, rfl⟩
    change IsUnit ((1 + (-t) • X) * y)
    rw [← hUi]
    exact (Units.isUnit (U t)⁻¹).mul (f.tsupport_subset ht.2)
  have hsub : tsupport f ⊆ (K : Set M) := by
    intro x hx
    refine ⟨((0 : ℝ), x), ⟨by norm_num, hx⟩, ?_⟩
    simp [A]
  let H (q : ℝ × M) := f ((1 + q.1 • X) * q.2)
  have hH : ContDiff ℝ ∞ H := f.contDiff.comp
    ((contDiff_const.add (contDiff_fst.smul contDiff_const)).mul contDiff_snd)
  let s := Ioo (-1 : ℝ) 1
  have h0 : (0 : ℝ) ∈ s := by norm_num [s]
  have hsupp (t : ℝ) (ht : t ∈ s) (x : M) (hx : x ∉ (K : Set M)) :
      H (t, x) = 0 := by
    by_contra h
    have hfx : (U t).val * x ∈ tsupport f := subset_tsupport f (by
      rw [hU]
      exact h)
    apply hx
    have ht' : t ∈ Icc (-1 : ℝ) 1 := Ioo_subset_Icc_self ht
    refine ⟨(t, (U t).val * x), ⟨ht', hfx⟩, ?_⟩
    change (1 + (-t) • X) * ((U t).val * x) = x
    rw [← hUi, ← mul_assoc, Units.inv_mul, one_mul]
  let v (t : ℝ) : 𝓓_{K}(M, ℂ) :=
    if ht : t ∈ s then
      ⟨fun x => H (t, x), hH.comp (contDiff_const.prodMk contDiff_id), hsupp t ht⟩
    else 0
  have hv (t : ℝ) (ht : t ∈ s) (x : M) : v t x = H (t, x) := by
    simp [v, ht]
    rfl
  let d := matrixLeftTestDerivative X f
  let g : 𝓓_{K}(M, ℂ) :=
    ⟨d, d.contDiff, fun x hx => by
      change d x = 0
      by_contra h
      exact hx (hsub (tsupport_matrixLeftTestDerivative_subset X f (subset_tsupport d h)))⟩
  have hg (x : M) : g x = fderiv ℝ H (0, x) (1, 0) := by
    have hpair : HasDerivAt (fun t : ℝ => (t, x)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
    have h₁ := ((hH.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hpair).deriv
    have hline : HasDerivAt (fun t : ℝ => (1 + t • X) * x) (X * x) 0 := by
      have he : (fun t : ℝ => (1 + t • X) * x) = fun t => x + t • (X * x) := by
        funext t
        rw [add_mul, one_mul, smul_mul_assoc]
      rw [he]
      simpa only [id_eq, one_smul] using (((hasDerivAt_id (0 : ℝ)).smul_const (X * x)).const_add x)
    have h₂ := ((f.contDiff.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hline).deriv
    have h₂' : deriv (fun t : ℝ => H (t, x)) 0 = d x := by
      simpa only [H, d, Function.comp_def, zero_smul, add_zero, one_mul,
        matrixLeftTestDerivative_apply] using h₂
    exact h₂'.symm.trans h₁
  let T' : 𝓓_{K}(M, ℂ) →L[ℝ] ℂ :=
    (T.comp (TestFunction.ofSupportedInCLM ℂ hK)).restrictScalars ℝ
  have h := Analysis.hasDerivAt_fixedSupportTestFamily isOpen_Ioo h0 hH v hv g hg T'
  change HasDerivAt _ (T d) 0 at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 from h0)] with t ht
  change T (matrixLeftTranslateTest (U t) f) = T (TestFunction.ofSupportedIn hK (v t))
  apply congrArg T
  ext x
  change f ((U t).val * x) = v t x
  rw [hU, hv t ht]

/-- The upper-root differential equation follows from covariance
under the actual upper-unipotent subgroup. -/
theorem matrixDistribution_upperRootDerivative
    (T : 𝓓(matrixUnitsOpen F (n + 1), ℂ) →L[ℂ] ℂ)
    (ψ : UnitaryAdditiveCharacter F) (a b : ℝ)
    (hψ : ∀ z : F, ψ z = Circle.exp (a * RCLike.re z + b * RCLike.im z))
    (hT : ∀ (u : upperUnipotent (n + 1) F) (f : 𝓓(matrixUnitsOpen F (n + 1), ℂ)),
      T (matrixLeftTranslateTest u.val f) = (Langlands.Whittaker.standardCharacter ψ n u : ℂ) * T f)
    (p : MatrixPositiveRoot (n + 1)) (z : F) (f : 𝓓(matrixUnitsOpen F (n + 1), ℂ)) :
    T (matrixLeftTestDerivative (Matrix.single p.val.1 p.val.2 z) f) =
      (((↑(if ∃ i : Fin n, i.castSucc = p.val.1 ∧ i.succ = p.val.2
          then a * RCLike.re z + b * RCLike.im z else 0) : ℂ) * Complex.I) * T f) := by
  have h₀ := hasDerivAt_upperRoot_distribution T p z f
  have h₁ := (hasDerivAt_standardCharacter_upperRootTransvection ψ a b hψ p z).mul_const (T f)
  have he := h₁.congr_of_eventuallyEq (Eventually.of_forall fun t =>
    hT (upperRootTransvection p (t • z)) f)
  exact h₀.unique he

end Langlands.Archimedean
