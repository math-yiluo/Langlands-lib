import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Lemmas
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Smooth parameter families on a compact space -/

noncomputable section
universe u v w z
open scoped Topology ContDiff
open Filter Set Topology
set_option autoImplicit false

namespace Langlands.Analysis

variable (X : Type u) [TopologicalSpace X] [CompactSpace X]
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous compact family of operators acts as an operator into continuous
functions, with its supremum norm as an operator bound. -/
def compactFamilyOperator (D : C(X, E →L[ℝ] F)) : E →L[ℝ] C(X, F) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun x => D x v, D.continuous.clm_apply continuous_const⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖D‖ (by
      intro v
      change ‖(⟨fun x => D x v, D.continuous.clm_apply continuous_const⟩ : C(X, F))‖
        ≤ ‖D‖ * ‖v‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg v))).2
      intro x
      exact ((D x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm x) (norm_nonneg v)))

@[simp]
theorem compactFamilyOperator_apply (D : C(X, E →L[ℝ] F)) (v : E) (x : X) :
    compactFamilyOperator X E F D v x = D x v := rfl

/-- The compact-family currying operation is continuous and real linear. -/
def compactFamilyOperatorCLM : C(X, E →L[ℝ] F) →L[ℝ] E →L[ℝ] C(X, F) :=
  LinearMap.mkContinuous
    { toFun := compactFamilyOperator X E F
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    1 (fun D => by
      simp only [one_mul]
      change ‖compactFamilyOperator X E F D‖ ≤ ‖D‖
      apply ContinuousLinearMap.opNorm_le_bound (compactFamilyOperator X E F D) (norm_nonneg D)
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      intro x
      exact ((D x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm x) (norm_nonneg v)))

@[simp]
theorem compactFamilyOperatorCLM_apply (D : C(X, E →L[ℝ] F)) (v : E) (x : X) :
    compactFamilyOperatorCLM X E F D v x = D x v := rfl

variable {X E F}

/-- A compact family of pointwise derivatives is the derivative in the supremum
norm when that family is continuous in the parameter. -/
theorem hasFDerivAt_compactFamily
    {f : E → C(X, F)} {D : E → C(X, E →L[ℝ] F)}
    {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    (hD : ContinuousOn D s)
    (hf : ∀ y ∈ s, ∀ t, HasFDerivAt (fun z => f z t) (D y t) y) :
    HasFDerivAt f (compactFamilyOperator X E F (D x)) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hxs : ∀ᶠ y in 𝓝 x, y ∈ s := hs.mem_nhds hx
  have hev : ∀ᶠ y in 𝓝 x, y ∈ s ∧ ‖D y - D x‖ < ε :=
    hxs.and
      ((hD.continuousAt (hs.mem_nhds hx)).tendsto.eventually
        (eventually_norm_sub_lt (D x) hε))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hev
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2
  intro t
  have hd : ∀ z ∈ Metric.ball x δ,
      HasFDerivWithinAt (fun z => f z t - D x t z)
        (D z t - D x t) (Metric.ball x δ) z := by
    intro z hz
    exact ((hf z (hb hz).1 t).sub (D x t).hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ z ∈ Metric.ball x δ, ‖D z t - D x t‖ ≤ ε := by
    intro z hz
    exact ((D z - D x).norm_coe_le_norm t).trans (hb hz).2.le
  have hm := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hbd (Metric.mem_ball_self hδ) hy
  simp only [ContinuousMap.sub_apply, compactFamilyOperator_apply,
    ContinuousLinearMap.map_sub]
  convert hm using 1
  congr 1
  abel

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Joint continuity restricts to continuity with values in compact continuous
functions. Only equality on the parameter domain is needed. -/
theorem continuousOn_compactFamily_of_joint
    {H : Type z} [TopologicalSpace H] (j : C(X, H))
    {h : E × H → F} {s : Set E} {t : Set H}
    (hj : ∀ a, j a ∈ t) (hh : ContinuousOn h (s ×ˢ t))
    {f : E → C(X, F)} (heq : ∀ y ∈ s, ∀ a, f y a = h (y, j a)) :
    ContinuousOn f s := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun p : s × X => h (p.1, j p.2)) :=
    hh.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk (j.continuous.comp continuous_snd))
      (fun p => ⟨p.1.property, hj p.2⟩)
  exact hc.congr (fun p => (heq p.1 p.1.property p.2).symm)

/-- A jointly finitely smooth function gives a smooth compact-restriction family
on any open parameter domain. -/
theorem contDiffOn_compactFamily_of_joint_aux
    {G : Type (max v w)} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H : Type z} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : C(X, H)) {s : Set E} {t : Set H} (hs : IsOpen s) (ht : IsOpen t)
    (hj : ∀ a, j a ∈ t) {m : ℕ} {h : E × H → G}
    (hh : ContDiffOn ℝ m h (s ×ˢ t))
    {f : E → C(X, G)} (heq : ∀ y ∈ s, ∀ a, f y a = h (y, j a)) :
    ContDiffOn ℝ m f s := by
  classical
  induction m generalizing G with
  | zero =>
    exact contDiffOn_zero.mpr (continuousOn_compactFamily_of_joint j hj hh.continuousOn heq)
  | succ m ih =>
    let d : E × H → E →L[ℝ] G := fun p =>
      (fderiv ℝ h p).comp (ContinuousLinearMap.inl ℝ E H)
    have hsm : (m : WithTop ℕ∞) + 1 ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by simp
    have hd : ContDiffOn ℝ m d (s ×ˢ t) :=
      (hh.fderiv_of_isOpen (hs.prod ht) hsm).clm_comp contDiffOn_const
    have hdcont (y : E) (hy : y ∈ s) : Continuous (fun a : X => d (y, j a)) :=
      hd.continuousOn.comp_continuous
        (continuous_const.prodMk j.continuous) (fun a => ⟨hy, hj a⟩)
    let D : E → C(X, E →L[ℝ] G) := fun y =>
      if hy : y ∈ s then ⟨fun a => d (y, j a), hdcont y hy⟩ else 0
    have hDeq : ∀ y ∈ s, ∀ a, D y a = d (y, j a) := by
      intro y hy a
      simp [D, hy]
    have hD : ContDiffOn ℝ m D s := ih hd hDeq
    have hpoint : ∀ y ∈ s, ∀ a,
        HasFDerivAt (fun z => f z a) (D y a) y := by
      intro y hy a
      have hhy : HasFDerivAt h (fderiv ℝ h (y, j a)) (y, j a) :=
        (hh.differentiableOn (by simp) (y, j a) ⟨hy, hj a⟩).differentiableAt
          ((hs.prod ht).mem_nhds ⟨hy, hj a⟩) |>.hasFDerivAt
      have hslice : HasFDerivAt (fun z => h (z, j a)) (d (y, j a)) y := by
        simpa only [d, Function.comp_def] using hhy.comp y
          ((hasFDerivAt_id y).prodMk (hasFDerivAt_const (j a) y))
      rw [hDeq y hy a]
      apply hslice.congr_of_eventuallyEq
      filter_upwards [hs.mem_nhds hy] with z hz
      exact heq z hz a
    have hfull : ∀ y ∈ s, HasFDerivAt f (compactFamilyOperator X E G (D y)) y :=
      fun y hy => hasFDerivAt_compactFamily hs hy hD.continuousOn hpoint
    simp only [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) hs.uniqueDiffOn).2
    refine ⟨by simp, fun y => compactFamilyOperator X E G (D y), ?_, ?_⟩
    · exact (compactFamilyOperatorCLM X E G).contDiff.comp_contDiffOn hD
    · exact fun y hy => (hfull y hy).hasFDerivWithinAt

/-- The finite-order compact-restriction theorem without a relation between
the parameter and value universes. -/
theorem contDiffOn_compactFamily_of_joint
    {H : Type z} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : C(X, H)) {s : Set E} {t : Set H} (hs : IsOpen s) (ht : IsOpen t)
    (hj : ∀ a, j a ∈ t) {m : ℕ} {h : E × H → F}
    (hh : ContDiffOn ℝ m h (s ×ˢ t))
    {f : E → C(X, F)} (heq : ∀ y ∈ s, ∀ a, f y a = h (y, j a)) :
    ContDiffOn ℝ m f s := by
  let U : F ≃L[ℝ] ULift.{v} F := ContinuousLinearEquiv.ulift.symm
  let liftF := ContinuousLinearMap.compLeftContinuous ℝ X U.toContinuousLinearMap
  have hU : ContDiffOn ℝ m (fun y => liftF (f y)) s := by
    apply contDiffOn_compactFamily_of_joint_aux j hs ht hj
      (U.contDiff.comp_contDiffOn hh)
    intro y hy a
    change U (f y a) = U (h (y, j a))
    rw [heq y hy a]
  have hdown := (ContinuousLinearMap.compLeftContinuous ℝ X
    U.symm.toContinuousLinearMap).contDiff.comp_contDiffOn hU
  convert hdown using 1
  ext y a
  exact (U.symm_apply_apply (f y a)).symm

/-- The compact-restriction version for smooth joint families. -/
theorem contDiffOn_infty_compactFamily_of_joint
    {H : Type z} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : C(X, H)) {s : Set E} {t : Set H} (hs : IsOpen s) (ht : IsOpen t)
    (hj : ∀ a, j a ∈ t) {h : E × H → F}
    (hh : ContDiffOn ℝ ∞ h (s ×ˢ t))
    {f : E → C(X, F)} (heq : ∀ y ∈ s, ∀ a, f y a = h (y, j a)) :
    ContDiffOn ℝ ∞ f s := by
  rw [contDiffOn_infty]
  intro m
  exact contDiffOn_compactFamily_of_joint j hs ht hj (hh.of_le (by simp)) heq

end Langlands.Analysis
