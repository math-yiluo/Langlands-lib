import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Smoothness in a closed linear submodule -/

noncomputable section
universe u
open scoped Topology ContDiff
open Filter Set
set_option autoImplicit false

namespace Langlands.Analysis

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem fderiv_mem_of_closedSubmodule
    {p : Submodule ℝ F} (hp : IsClosed (p : Set F)) {f : E → p}
    {D : E →L[ℝ] F} {x : E} (h : HasFDerivAt (fun y => (f y).val) D x)
    (v : E) : D v ∈ p := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  have hcomp : HasDerivAt (fun t : ℝ => (f (x + t • v)).val) (D v) 0 :=
    h.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hp.mem_of_tendsto hcomp.tendsto_slope_zero
    (Eventually.of_forall fun t => p.smul_mem _ (p.sub_mem
      (f (x + (0 + t) • v)).property (f (x + (0 : ℝ) • v)).property))

private theorem hasFDerivAt_codRestrict
    {p : Submodule ℝ F} {f : E → p} {D : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt (fun y => (f y).val) D x) (hD : ∀ v, D v ∈ p) :
    HasFDerivAt f (D.codRestrict p hD) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h ⊢
  exact h

/-- Operators whose image lies in a specified submodule. -/
private def operatorsInto (p : Submodule ℝ F) : Submodule ℝ (E →L[ℝ] F) where
  carrier := {D | ∀ v, D v ∈ p}
  zero_mem' := fun _ => p.zero_mem
  add_mem' hD hL v := p.add_mem (hD v) (hL v)
  smul_mem' c _ hD v := p.smul_mem c (hD v)

private theorem isClosed_operatorsInto {p : Submodule ℝ F}
    (hp : IsClosed (p : Set F)) : IsClosed (operatorsInto (E := E) p : Set (E →L[ℝ] F)) := by
  have hset : (operatorsInto (E := E) p : Set (E →L[ℝ] F)) =
      ⋂ v : E, (fun D : E →L[ℝ] F => D v) ⁻¹' (p : Set F) := by
    ext D
    change (∀ v, D v ∈ p) ↔ D ∈ ⋂ v : E, (fun L : E →L[ℝ] F => L v) ⁻¹' (p : Set F)
    simp only [mem_iInter, mem_preimage]
    rfl
  rw [hset]
  exact isClosed_iInter fun v => hp.preimage (ContinuousLinearMap.apply ℝ F v).continuous

/-- Restricting an operator to its submodule-valued form preserves the norm bound. -/
private def codRestrictOperator (p : Submodule ℝ F) :
    operatorsInto (E := E) p →L[ℝ] E →L[ℝ] p :=
  LinearMap.mkContinuous
    { toFun := fun D : operatorsInto (E := E) p => D.val.codRestrict p D.property
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
    1 (fun D => by
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
      intro v
      exact D.val.le_opNorm v)

/-- On an open set, finite smoothness into a closed submodule can be checked
after inclusion in the ambient normed space. -/
theorem contDiffOn_nat_of_closedSubmodule
    {p : Submodule ℝ F} (hp : IsClosed (p : Set F)) {f : E → p}
    {s : Set E} (hs : IsOpen s) {m : ℕ}
    (hf : ContDiffOn ℝ m (fun x => (f x).val) s) : ContDiffOn ℝ m f s := by
  classical
  induction m generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    exact Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hf.continuousOn
  | succ m ih =>
    rw [Nat.cast_succ] at hf ⊢
    obtain ⟨hdiff, _, hDcont⟩ := (contDiffOn_succ_iff_fderiv_of_isOpen hs).mp hf
    let D₀ : E → E →L[ℝ] F := fderiv ℝ (fun x => (f x).val)
    have hD (x : E) (hx : x ∈ s) : HasFDerivAt (fun y => (f y).val) (D₀ x) x :=
      ((hdiff x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt
    let D : E → operatorsInto (E := E) p := fun x =>
      if hx : x ∈ s then ⟨D₀ x, fderiv_mem_of_closedSubmodule hp (hD x hx)⟩ else 0
    have hD_eq (x : E) (hx : x ∈ s) :
        D x = ⟨D₀ x, fderiv_mem_of_closedSubmodule hp (hD x hx)⟩ := by
      simp [D, hx]
    have hD_smooth : ContDiffOn ℝ m D s :=
      ih (isClosed_operatorsInto hp)
        (hDcont.congr fun x hx => congrArg Subtype.val (hD_eq x hx))
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn).mpr
    refine ⟨by simp, fun x => codRestrictOperator p (D x), ?_, ?_⟩
    · have hrestrict : ContDiff ℝ m
          (codRestrictOperator (E := E) p : operatorsInto p → E →L[ℝ] p) :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ↥(operatorsInto (E := E) p))
          (F := E →L[ℝ] p) (n := (m : WithTop ℕ∞))
          (codRestrictOperator (E := E) p)
      exact hrestrict.comp_contDiffOn hD_smooth
    · intro x hx
      change HasFDerivWithinAt f (codRestrictOperator p (D x)) s x
      rw [hD_eq x hx]
      exact (hasFDerivAt_codRestrict (hD x hx)
        (fderiv_mem_of_closedSubmodule hp (hD x hx))).hasFDerivWithinAt

/-- Smoothness into a closed submodule on an open set follows from ambient
smoothness. -/
theorem contDiffOn_infty_of_closedSubmodule
    {p : Submodule ℝ F} (hp : IsClosed (p : Set F)) {f : E → p}
    {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ (fun x => (f x).val) s) : ContDiffOn ℝ ∞ f s := by
  rw [contDiffOn_infty]
  intro m
  exact contDiffOn_nat_of_closedSubmodule hp hs (hf.of_le (by simp))

/-- Ambient smoothness characterizes smoothness into a closed submodule. -/
def ClosedSubmoduleSmoothnessStatement : Prop :=
  ∀ (p : Submodule ℝ F), IsClosed (p : Set F) →
    ∀ (f : E → p) (s : Set E), IsOpen s →
      (ContDiffOn ℝ ∞ (fun x => (f x).val) s ↔ ContDiffOn ℝ ∞ f s)

theorem closedSubmoduleSmoothness : ClosedSubmoduleSmoothnessStatement (E := E) (F := F) := by
  intro p hp f s hs
  refine ⟨contDiffOn_infty_of_closedSubmodule hp hs, fun hf => ?_⟩
  exact p.subtypeL.contDiff.comp_contDiffOn hf

end Langlands.Analysis
