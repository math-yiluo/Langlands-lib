import Langlands.Representation.Archimedean.RealCartanOffBlockDeterminant
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Invariance of the normalized product across Cartan blocks -/

noncomputable section

set_option autoImplicit false

open Matrix
open scoped Sym2

namespace Langlands.Archimedean.RealCartanOffBlockDeterminant

private theorem normalizedRatio_eq_of_conj {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W] (e : V ≃ₗ[ℝ] W)
    (L : Module.End ℝ V) (L' : Module.End ℝ W)
    (h : L' = e.toLinearMap.comp (L.comp e.symm.toLinearMap)) :
    |LinearMap.det (1 - L')| / Real.sqrt |LinearMap.det L'| =
      |LinearMap.det (1 - L)| / Real.sqrt |LinearMap.det L| := by
  have h₀ : 1 - L' = e.toLinearMap.comp ((1 - L).comp e.symm.toLinearMap) := by
    rw [h]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, map_sub, LinearEquiv.apply_symm_apply]
  rw [h₀, LinearMap.det_conj, h, LinearMap.det_conj]

/-- Conjugating the two square blocks preserves their normalized off-block factor. -/
theorem normalizedOffBlockDet_conj {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (g a : (Matrix ι ι ℝ)ˣ) (h b : (Matrix κ κ ℝ)ˣ) :
    normalizedOffBlockDet (a * g * a⁻¹) (b * h * b⁻¹) = normalizedOffBlockDet g h := by
  apply normalizedRatio_eq_of_conj (offBlockAction a b).symm
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
    offBlockAction_apply, offBlockAction_symm_apply, _root_.mul_inv_rev, inv_inv, Units.val_mul,
    Matrix.mul_assoc]

/-- Reindexing the coordinates of the two square blocks preserves their normalized factor. -/
theorem normalizedOffBlockDet_reindex {ι ι' κ κ' : Type*}
    [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ] [DecidableEq κ']
    (e : ι ≃ ι') (f : κ ≃ κ') (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ) :
    normalizedOffBlockDet (Units.map (reindexRingEquiv ℝ e).toMonoidHom g)
      (Units.map (reindexRingEquiv ℝ f).toMonoidHom h) = normalizedOffBlockDet g h := by
  let T := reindexLinearEquiv ℝ ℝ e f
  apply normalizedRatio_eq_of_conj T
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, offBlockAction_apply, ← map_inv]
  change (g⁻¹.val.submatrix e.symm e.symm) * X * (h.val.submatrix f.symm f.symm) =
    (g⁻¹.val * X.submatrix e f * h.val).submatrix e.symm f.symm
  have hleft : (g⁻¹.val.submatrix e.symm e.symm) * X =
      (g⁻¹.val * X.submatrix e f).submatrix e.symm f.symm := by
    rw [← submatrix_mul_equiv g⁻¹.val (X.submatrix e f) e.symm e.symm f.symm,
      submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, submatrix_id_id]
  rw [hleft, submatrix_mul_equiv (g⁻¹.val * X.submatrix e f) h.val e.symm f.symm f.symm]

/-- Distinct squared radii make the identity minus the off-block action invertible
at the determinant level. -/
theorem det_one_sub_offBlockAction_ne_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ) {a b : ℝ}
    (hg : g.valᵀ * g.val = a • 1) (hh : h.val * h.valᵀ = b • 1) (hab : a ≠ b) :
    LinearMap.det (1 - (offBlockAction g h).toLinearMap) ≠ 0 := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro X hX
  change X - offBlockAction g h X = 0 at hX
  have hrel : g.val * X = X * h.val := calc
    _ = g.val * (g⁻¹.val * X * h.val) := congrArg (g.val * ·) (sub_eq_zero.mp hX)
    _ = (g.val * g⁻¹.val) * X * h.val := by simp only [Matrix.mul_assoc]
    _ = _ := by simp
  have hleft : trace ((g.val * X)ᵀ * (g.val * X)) = a * trace (Xᵀ * X) := calc
    _ = trace (Xᵀ * (g.valᵀ * g.val) * X) := by simp only [transpose_mul, Matrix.mul_assoc]
    _ = _ := by
      simp only [hg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, trace_smul, smul_eq_mul]
  have hright : trace ((X * h.val)ᵀ * (X * h.val)) = b * trace (Xᵀ * X) := calc
    _ = trace (h.valᵀ * ((Xᵀ * X) * h.val)) := by simp only [transpose_mul, Matrix.mul_assoc]
    _ = trace ((Xᵀ * X) * (h.val * h.valᵀ)) := by rw [trace_mul_comm h.valᵀ, Matrix.mul_assoc]
    _ = _ := by simp only [hh, Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul]
  have hs := hleft.symm.trans ((congrArg (fun A : Matrix ι κ ℝ => trace (Aᵀ * A)) hrel).trans hright)
  have hz : trace (Xᵀ * X) = 0 :=
    (mul_eq_zero.mp (show (a - b) * trace (Xᵀ * X) = 0 by linarith)).resolve_left (sub_ne_zero.mpr hab)
  exact trace_conjTranspose_mul_self_eq_zero_iff.mp (by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hz)

theorem normalizedOffBlockDet_ne_zero_of_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ) {a b : ℝ}
    (hg : g.valᵀ * g.val = a • 1) (hh : h.val * h.valᵀ = b • 1) (hab : a ≠ b) :
    normalizedOffBlockDet g h ≠ 0 := by
  have hdet := (LinearEquiv.det (offBlockAction g h)).ne_zero
  rw [LinearEquiv.coe_det] at hdet
  exact div_ne_zero (abs_ne_zero.mpr (det_one_sub_offBlockAction_ne_zero g h hg hh hab))
    (Real.sqrt_pos.2 (abs_pos.mpr hdet)).ne'

section Product

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private def unorderedFactor (d : α → ℕ) (g : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℝ)ˣ) :
    Sym2 α → ℝ :=
  Sym2.lift ⟨fun i j => normalizedOffBlockDet (g i) (g j),
    fun i j => (normalizedOffBlockDet_swap (g i) (g j)).symm⟩

/-- The normalized product indexed by unordered pairs of distinct blocks. -/
def normalizedOffBlockProduct (d : α → ℕ)
    (g : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℝ)ˣ) : ℝ :=
  ∏ p : {p : Sym2 α // ¬ p.IsDiag}, unorderedFactor d g p.val

/-- Distinct Gram scalars across the blocks give a nonzero normalized product. -/
theorem normalizedOffBlockProduct_ne_zero_of_gram (d : α → ℕ)
    (g : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℝ)ˣ) (a : α → ℝ)
    (hg : ∀ i, (g i).valᵀ * (g i).val = (a i) • 1 ∧ (g i).val * (g i).valᵀ = (a i) • 1)
    (ha : Function.Injective a) :
    normalizedOffBlockProduct d g ≠ 0 := by
  unfold normalizedOffBlockProduct
  refine Finset.prod_ne_zero_iff.mpr fun ⟨p, hp⟩ _ => ?_
  induction p using Sym2.ind with
  | _ i j =>
    have hne : i ≠ j := fun he => hp (Sym2.mk_isDiag_iff.mpr he)
    exact normalizedOffBlockDet_ne_zero_of_gram (g i) (g j) (hg i).1 (hg j).2 (ha.ne hne)

/-- The product is unchanged by permuting block labels. -/
theorem normalizedOffBlockProduct_equiv (e : β ≃ α) (d : α → ℕ)
    (g : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℝ)ˣ) :
    normalizedOffBlockProduct (d ∘ e) (fun i => g (e i)) = normalizedOffBlockProduct d g := by
  let E : Sym2 β ≃ Sym2 α :=
    { toFun := Sym2.map e
      invFun := Sym2.map e.symm
      left_inv := Sym2.ind (fun i j => by simp)
      right_inv := Sym2.ind (fun i j => by simp) }
  let T : {p : Sym2 β // ¬ p.IsDiag} ≃ {p : Sym2 α // ¬ p.IsDiag} :=
    E.subtypeEquiv fun p => by
      change ¬ p.IsDiag ↔ ¬ (Sym2.map e p).IsDiag
      exact (Sym2.isDiag_map e.injective (z := p)).not.symm
  unfold normalizedOffBlockProduct
  refine Fintype.prod_equiv T _ _ ?_
  rintro ⟨p, hp⟩
  exact (Sym2.lift_map_apply
    ⟨fun i j => normalizedOffBlockDet (g i) (g j),
      fun i j => (normalizedOffBlockDet_swap (g i) (g j)).symm⟩ p).symm

/-- A size-preserving assignment and independent changes of basis on the assigned
blocks preserve the normalized product. -/
theorem normalizedOffBlockProduct_eq_of_assignment (e : β ≃ α) (d : α → ℕ) (d' : β → ℕ)
    (he : ∀ i, d (e i) = d' i)
    (g : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℝ)ˣ)
    (k : ∀ i, (Matrix (Fin (d' i)) (Fin (d' i)) ℝ)ˣ) :
    normalizedOffBlockProduct d'
        (fun i => k i * Units.map (reindexRingEquiv ℝ (finCongr (he i))).toMonoidHom
          (g (e i)) * (k i)⁻¹) =
      normalizedOffBlockProduct d g := by
  let a (i : β) := Units.map (reindexRingEquiv ℝ (finCongr (he i))).toMonoidHom (g (e i))
  change normalizedOffBlockProduct d' (fun i => k i * a i * (k i)⁻¹) = _
  rw [← normalizedOffBlockProduct_equiv e d g]
  unfold normalizedOffBlockProduct
  refine Finset.prod_congr rfl fun ⟨p, _⟩ _ => ?_
  induction p using Sym2.ind with
  | _ i j =>
    change normalizedOffBlockDet (k i * a i * (k i)⁻¹) (k j * a j * (k j)⁻¹) =
      normalizedOffBlockDet (g (e i)) (g (e j))
    rw [normalizedOffBlockDet_conj]
    exact normalizedOffBlockDet_reindex (finCongr (he i)) (finCongr (he j)) (g (e i)) (g (e j))

private def strictSortEquiv {α : Type*} [LinearOrder α] :
    {p : Sym2 α // ¬ p.IsDiag} ≃ {p : α × α // p.1 < p.2} where
  toFun p := ⟨(p.val.inf, p.val.sup), by
    obtain ⟨z, hz⟩ := p
    induction z using Sym2.ind with
    | _ i j =>
      have hne : i ≠ j := fun he => hz (Sym2.mk_isDiag_iff.mpr he)
      rcases lt_or_gt_of_ne hne with h | h
      · simpa [min_eq_left h.le, max_eq_right h.le] using h
      · simpa [min_eq_right h.le, max_eq_left h.le] using h⟩
  invFun p := ⟨s(p.val.1, p.val.2), fun h => p.property.ne (Sym2.mk_isDiag_iff.mp h)⟩
  left_inv p := Subtype.ext (Sym2.sortEquiv.left_inv p.val)
  right_inv p := Subtype.ext (Prod.ext (min_eq_left p.property.le) (max_eq_right p.property.le))

/-- In an ordered block decomposition the product is taken once for each increasing pair. -/
theorem normalizedOffBlockProduct_eq_ordered {α : Type*} [Fintype α] [LinearOrder α]
    (d : α → ℕ) (g : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℝ)ˣ) :
    normalizedOffBlockProduct d g = ∏ p : {p : α × α // p.1 < p.2},
      normalizedOffBlockDet (g p.val.1) (g p.val.2) := by
  unfold normalizedOffBlockProduct
  refine Fintype.prod_equiv strictSortEquiv _ _ ?_
  rintro ⟨p, hp⟩
  induction p using Sym2.ind with
  | _ i j =>
    change normalizedOffBlockDet (g i) (g j) =
      normalizedOffBlockDet (g (min i j)) (g (max i j))
    rcases le_total i j with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, normalizedOffBlockDet_swap (g i) (g j)]

/-- The decreasing pairs of a lower block chart give the same normalized product. -/
theorem normalizedOffBlockProduct_eq_lower {α : Type*} [Fintype α] [LinearOrder α]
    (d : α → ℕ) (g : ∀ i, (Matrix (Fin (d i)) (Fin (d i)) ℝ)ˣ) :
    normalizedOffBlockProduct d g = ∏ p : {p : α × α // p.2 < p.1},
      normalizedOffBlockDet (g p.val.1) (g p.val.2) := by
  rw [normalizedOffBlockProduct_eq_ordered]
  let e : {p : α × α // p.1 < p.2} ≃ {p : α × α // p.2 < p.1} :=
    (Equiv.prodComm α α).subtypeEquiv (fun _ => Iff.rfl)
  exact Fintype.prod_equiv e _ _ fun p => (normalizedOffBlockDet_swap (g p.val.1) (g p.val.2)).symm

end Product

end Langlands.Archimedean.RealCartanOffBlockDeterminant
