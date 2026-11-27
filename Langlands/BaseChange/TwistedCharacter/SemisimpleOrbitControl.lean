import Langlands.BaseChange.TwistedCharacter.SemisimpleSlice
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Uniform transverse control for semisimple descent -/

noncomputable section

namespace Langlands.BaseChange

open ContinuousLinearMap Filter Function
open scoped _root_.Topology

variable {F R : Type*} [NontriviallyNormedField F] [CompleteSpace F] [NormedRing R]
  [NormedAlgebra F R] [FiniteDimensional F R]

/-- The adjoint action at the product of a fixed unit and the semisimple center. -/
def fixedUnitAdjoint (α : R ≃ₐ[F] R) (m : (adjointFixedAlgebra α)ˣ) : R →L[F] R :=
  (mulLeftRight F R (m.val : R) ((m⁻¹ : (adjointFixedAlgebra α)ˣ).val : R)).comp
    α.toLinearMap.toContinuousLinearMap

@[simp] theorem fixedUnitAdjoint_apply (α : R ≃ₐ[F] R) (m : (adjointFixedAlgebra α)ˣ) (x : R) :
    fixedUnitAdjoint α m x = (m.val : R) * α x * ((m⁻¹ : (adjointFixedAlgebra α)ˣ).val : R) := rfl

private theorem continuous_fixedUnitAdjoint (α : R ≃ₐ[F] R) : Continuous (fixedUnitAdjoint α) := by
  let S := adjointFixedAlgebra α
  have hv : Continuous fun m : Sˣ => (m.val : R) := continuous_subtype_val.comp Units.continuous_val
  exact ((mulLeftRight F R).continuous.comp hv |>.clm_apply (hv.comp continuous_inv)).clm_comp
    continuous_const

/-- A projection onto the fixed algebra with a uniform inverse estimate on the
transverse displacement under the adjoint actions at nearby slice points. -/
def SemisimpleTransverseEstimateStatement (α : R ≃ₐ[F] R) : Prop :=
  Module.End.IsSemisimple α.toLinearMap →
  ∃ (p : R →L[F] R) (C : ℝ), 0 ≤ C ∧ (∀ x, α (p x) = p x) ∧
    (∀ x, α x = x → p x = x) ∧ (∀ x, p (α x) = p x) ∧
    ∀ᶠ m : (adjointFixedAlgebra α)ˣ in 𝓝 1, ∀ x : R,
      ‖x - p x‖ ≤ C * ‖fixedUnitAdjoint α m x - x‖

theorem semisimpleTransverseEstimate (α : R ≃ₐ[F] R) : SemisimpleTransverseEstimateStatement α := by
  intro hα
  let S := adjointFixedAlgebra α
  let s := S.toSubmodule
  have hs : s ∈ Module.End.invtSubmodule α.toLinearMap := by
    rw [Module.End.mem_invtSubmodule]
    intro x hx
    change α x = x at hx
    change α x ∈ s
    rwa [hx]
  obtain ⟨q, hq, hsq⟩ := Module.End.isSemisimple_iff.mp hα s hs
  have hq' := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem α.toLinearMap).mp hq
  let E : R ≃L[F] (s × q) := (s.prodEquivOfIsCompl q hsq).symm.toContinuousLinearEquiv
  let P : R →L[F] s := (fst F s q).comp E.toContinuousLinearMap
  let Q : R →L[F] q := (snd F s q).comp E.toContinuousLinearMap
  let p : R →L[F] R := s.subtype.toContinuousLinearMap.comp P
  have hPQ (x : R) : p x + (Q x : R) = x :=
    (s.prodEquivOfIsCompl q hsq).apply_symm_apply x
  have hP (y : s) : p (y : R) = (y : R) := by
    change ((s.prodEquivOfIsCompl q hsq).symm y.val).1.val = y.val
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  have hPq (z : q) : p (z : R) = 0 := by
    change ((s.prodEquivOfIsCompl q hsq).symm z.val).1.val = 0
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
    rfl
  have hQs (y : s) : Q (y : R) = 0 := by
    change ((s.prodEquivOfIsCompl q hsq).symm y.val).2 = 0
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  have hQ (z : q) : Q (z : R) = z := by
    change ((s.prodEquivOfIsCompl q hsq).symm z.val).2 = z
    rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  have hpS (x : R) : α (p x) = p x := (P x).property
  have hpα (x : R) : p (α x) = p x := by
    conv_lhs =>
      rw [← hPQ x, map_add, map_add, hpS, hPq ⟨α (Q x : R), hq' _ (Q x).property⟩, add_zero]
    exact hP (P x)
  let d : q →ₗ[F] q := α.toLinearMap.restrict hq' - LinearMap.id
  have hd : Injective d := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hxval : α (x : R) = (x : R) := sub_eq_zero.mp (congrArg Subtype.val hx : α x.val - x.val = 0)
    exact Subtype.ext (Submodule.disjoint_def.mp hsq.disjoint x.val hxval x.property)
  let e := (d.linearEquivOfInjective hd rfl).toContinuousLinearEquiv
  let M (m : Sˣ) : q →L[F] q :=
    Q.comp ((fixedUnitAdjoint α m - ContinuousLinearMap.id F R).comp q.subtype.toContinuousLinearMap)
  have hM (m : Sˣ) (z : q) : M m z = Q (fixedUnitAdjoint α m (z : R) - z) := rfl
  have hM1 : M 1 = e.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    rw [hM, fixedUnitAdjoint_apply]
    simp only [Units.val_one, inv_one, Subalgebra.coe_one, one_mul, mul_one]
    exact hQ (d z)
  let N (m : Sˣ) : q →L[F] q := e.symm.toContinuousLinearMap.comp (M m) - ContinuousLinearMap.id F q
  have hN1 : N 1 = 0 := by
    simp only [N, hM1]
    apply ContinuousLinearMap.ext
    intro x
    change e.symm (e x) - x = 0
    rw [e.symm_apply_apply, sub_self]
  have hM' : Continuous M :=
    (continuous_const (y := Q)).clm_comp
      (((continuous_fixedUnitAdjoint α).sub (continuous_const (y := ContinuousLinearMap.id F R))).clm_comp
        (continuous_const (y := q.subtype.toContinuousLinearMap)))
  have hN : Continuous N :=
    ((continuous_const (y := e.symm.toContinuousLinearMap)).clm_comp hM').sub
      (continuous_const (y := ContinuousLinearMap.id F q))
  have hsmall : ∀ᶠ m : Sˣ in 𝓝 1, ‖N m‖ < (1 : ℝ) / 2 := by
    have hlt : ‖N 1‖ < (1 : ℝ) / 2 := by
      rw [hN1, ContinuousLinearMap.opNorm_zero]
      norm_num
    let opNormed : SeminormedAddCommGroup (q →L[F] q) :=
      ContinuousLinearMap.toSeminormedAddCommGroup (E := q) (F := q) (σ₁₂ := RingHom.id F)
    have hcNorm : Continuous (norm : (q →L[F] q) → ℝ) :=
      @continuous_norm _ opNormed.toSeminormedAddGroup
    have ht : ContinuousAt (fun m : Sˣ => ‖N m‖) 1 := (hcNorm.comp hN).continuousAt
    exact ht.eventually (gt_mem_nhds hlt)
  let C := 2 * ‖e.symm.toContinuousLinearMap‖ * ‖Q‖
  refine ⟨p, C, by dsimp [C]; positivity, hpS, fun x hx => hP ⟨x, hx⟩, hpα, ?_⟩
  filter_upwards [hsmall] with m hm x
  let z := Q x
  have hsplit : x - p x = (z : R) := sub_eq_iff_eq_add.mpr ((add_comm _ _).trans (hPQ x)).symm
  have hsv : fixedUnitAdjoint α m (p x) - p x ∈ s := by
    let y : S := m.val * ⟨p x, hpS x⟩ * (m⁻¹ : Sˣ).val - ⟨p x, hpS x⟩
    have hy : (y : R) = fixedUnitAdjoint α m (p x) - p x := by
      simp only [y, fixedUnitAdjoint_apply, Subalgebra.coe_sub, Subalgebra.coe_mul, hpS]
    rw [← hy]
    exact y.property
  have hz : M m z = Q (fixedUnitAdjoint α m x - x) := by
    rw [hM]
    have h := hQs ⟨_, hsv⟩
    change Q (fixedUnitAdjoint α m (p x) - p x) = 0 at h
    conv_rhs => rw [← hPQ x, map_add, add_sub_add_comm, map_add, h, zero_add]
  have hbound : ‖N m z‖ ≤ (1 / 2 : ℝ) * ‖z‖ :=
    (ContinuousLinearMap.le_opNorm (N m) z).trans (mul_le_mul_of_nonneg_right hm.le (norm_nonneg _))
  have hn : e.symm (M m z) - N m z = z := by
    change e.symm (M m z) - (e.symm (M m z) - z) = z
    abel
  have ht : ‖z‖ ≤ ‖e.symm (M m z)‖ + (1 / 2 : ℝ) * ‖z‖ := calc
    _ = ‖e.symm (M m z) - N m z‖ := congrArg norm hn.symm
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add_right hbound _)
  calc
    ‖x - p x‖ = ‖z‖ := by rw [hsplit]; rfl
    _ ≤ 2 * ‖e.symm (M m z)‖ := by linarith
    _ ≤ 2 * (‖e.symm.toContinuousLinearMap‖ * ‖M m z‖) :=
      mul_le_mul_of_nonneg_left (e.symm.toContinuousLinearMap.le_opNorm _) (by norm_num)
    _ ≤ 2 * (‖e.symm.toContinuousLinearMap‖ * (‖Q‖ * ‖fixedUnitAdjoint α m x - x‖)) := by
      rw [hz]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Q.le_opNorm _) (ContinuousLinearMap.opNorm_nonneg _)) (by norm_num)
    _ = C * ‖fixedUnitAdjoint α m x - x‖ := by dsimp [C]; ring

end Langlands.BaseChange
