import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.RegularMatrixSlice
import Langlands.BaseChange.WeylIntegrationData
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # The linear differential in ordinary Weyl coordinates -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands
open LinearMap Matrix Module _root_.Polynomial

universe u

private abbrev Mat (F : Type u) (n : ℕ) := Matrix (Fin n) (Fin n) F

variable {F : Type u} [Field F] {n : ℕ}

/-- The ordinary adjoint action minus the identity on the matrix algebra. -/
def adjointDefect (γ : GeneralLinear n F) : Module.End F (Mat F n) :=
  linearAdjoint γ - LinearMap.id

theorem adjointDefect_apply (γ : GeneralLinear n F) (X : Mat F n) :
    adjointDefect γ X = γ.val * X * (γ⁻¹ : GeneralLinear n F).val - X := by
  change γ.val * (X * (γ⁻¹ : GeneralLinear n F).val) - X = _
  rw [mul_assoc]

/-- The kernel of the adjoint defect is the matrix centralizer. -/
theorem mem_ker_adjointDefect_iff (γ : GeneralLinear n F) (X : Mat F n) :
    X ∈ (adjointDefect γ).ker ↔ Commute X γ.val := by
  rw [LinearMap.mem_ker, adjointDefect_apply, sub_eq_zero]
  constructor
  · intro h
    have h' := congrArg (· * γ.val) h
    simpa only [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one,
      commute_iff_eq, eq_comm] using h'
  · intro h
    rw [← h.eq, mul_assoc X, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

/-- The matrix centralizer of a regular semisimple element has dimension `n`. -/
theorem finrank_ker_adjointDefect (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ) :
    Module.finrank F (adjointDefect γ).ker = n := by
  obtain ⟨v, hv⟩ := regularCyclicBasis F n γ.val hγ
  let e : (adjointDefect γ).ker →ₗ[F] (Fin n → F) :=
    { toFun := fun X => X.val *ᵥ v
      map_add' := fun X Y => Matrix.add_mulVec X.val Y.val v
      map_smul' := fun a X => Matrix.smul_mulVec a X.val v }
  have he : Function.Bijective e := by
    constructor
    · intro X Y h
      apply Subtype.ext
      exact eq_of_commute_mulVec_eq hv
        ((mem_ker_adjointDefect_iff γ _).mp X.property)
        ((mem_ker_adjointDefect_iff γ _).mp Y.property) h
    · intro y
      obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hv) y
      let X := ∑ j : Fin n, c j • γ.val ^ (j : ℕ)
      have hX : Commute X γ.val :=
        Commute.sum_left _ _ _ fun j _ => ((Commute.refl γ.val).pow_left _).smul_left _
      refine ⟨⟨X, (mem_ker_adjointDefect_iff γ _).mpr hX⟩, ?_⟩
      change X *ᵥ v = y
      rw [← hc, show X *ᵥ v = ∑ j : Fin n, c j • (cyclicBasisMatrix γ.val v).col j by
        simp only [X, sum_mulVec, smul_mulVec, cyclicBasisMatrix_col]]
      ext i
      simp only [mulVec_apply_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.col_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    (LinearEquiv.ofBijective e he).finrank_eq

/-- At a regular semisimple matrix the centralizer and adjoint defect image
give complementary matrix subspaces. -/
theorem isCompl_ker_range_adjointDefect (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ) :
    IsCompl (adjointDefect γ).ker (adjointDefect γ).range := by
  let d := adjointDefect γ
  have hs : d.ker ⊔ d.range = ⊤ := by
    apply top_unique
    intro Y _
    obtain ⟨X, c, h⟩ := exists_commutator_add_powers γ.val hγ Y
    have hp : (∑ j : Fin n, c j • γ.val ^ (j : ℕ)) ∈ d.ker :=
      (mem_ker_adjointDefect_iff γ _).mpr
        (Commute.sum_left _ _ _ fun j _ => ((Commute.refl γ.val).pow_left _).smul_left _)
    have hc : X * γ.val - γ.val * X ∈ d.range := by
      refine ⟨-(X * γ.val), ?_⟩
      have hi : γ.val * (γ⁻¹ : GeneralLinear n F).val = 1 :=
        congrArg Units.val (mul_inv_cancel γ)
      rw [show d = adjointDefect γ by rfl, adjointDefect_apply, mul_neg, neg_mul, mul_assoc,
        mul_assoc X, hi, mul_one, sub_neg_eq_add, neg_add_eq_sub]
    rw [← h, add_comm]
    exact Submodule.add_mem_sup hp hc
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq d.ker d.range
  rw [hs, finrank_top, add_comm (Module.finrank F d.ker),
    d.finrank_range_add_finrank_ker] at hdim
  have hzero : Module.finrank F (d.ker ⊓ d.range : Submodule F (Mat F n)) = 0 := by
    omega
  exact ⟨disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hzero),
    codisjoint_iff.mpr hs⟩

section SplitEndomorphism

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem det_neg_eq_charpoly_coeff_zero (f : Module.End F V) :
    (-f).det = f.charpoly.coeff 0 := by
  simpa only [Polynomial.coeff_zero_eq_eval_zero, map_zero, zero_sub] using
    (f.eval_charpoly 0).symm

/-- For a split kernel and range, replacing the zero block by the identity
and negating the range block gives the first nonzero characteristic coefficient. -/
theorem det_projection_sub_of_isCompl (d : Module.End F V) (h : IsCompl d.ker d.range) :
    IsUnit (d.ker.projection d.range h - d).det ∧
      (d.ker.projection d.range h - d).det = d.charpoly.coeff (Module.finrank F d.ker) := by
  let r : Module.End F d.range := d.restrict fun x _ => ⟨x, rfl⟩
  let e := Submodule.prodEquivOfIsCompl d.ker d.range h
  have hker (x : d.ker) : d x.val = 0 := LinearMap.mem_ker.mp x.property
  have hd : d = e.conj ((0 : Module.End F d.ker).prodMap r) := by
    ext x
    obtain ⟨⟨p, q⟩, rfl⟩ := e.surjective x
    change d (p.val + q.val) = e (((0 : Module.End F d.ker).prodMap r) (e.symm (e (p, q))))
    rw [e.symm_apply_apply, map_add, hker, zero_add]
    simp [e, r, Submodule.coe_prodEquivOfIsCompl']
    rfl
  have hp : d.ker.projection d.range h - d =
      e.conj ((LinearMap.id : Module.End F d.ker).prodMap (-r)) := by
    ext x
    obtain ⟨⟨p, q⟩, rfl⟩ := e.surjective x
    change (d.ker.projection d.range h - d) (p.val + q.val) =
      e (((LinearMap.id : Module.End F d.ker).prodMap (-r)) (e.symm (e (p, q))))
    rw [e.symm_apply_apply, LinearMap.sub_apply, map_add, map_add, hker, zero_add,
      Submodule.projection_apply_left, Submodule.projection_apply_right, add_zero]
    simp [e, r, Submodule.coe_prodEquivOfIsCompl', sub_eq_add_neg]
    rfl
  have hdet := LinearMap.det_conj ((LinearMap.id : Module.End F d.ker).prodMap (-r)) e
  rw [← LinearMap.comp_assoc, ← LinearEquiv.conj_apply] at hdet
  rw [hp, hdet, LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  constructor
  · have hinj : Function.Injective (-r) := by
      apply (LinearMap.ker_eq_bot).mp
      apply bot_unique
      intro x hx
      have hxker : x.val ∈ d.ker := by
        rw [LinearMap.mem_ker] at hx ⊢
        have hn : -(d x.val) = 0 := congrArg Subtype.val hx
        exact neg_eq_zero.mp hn
      have hz : x.val = 0 :=
        h.disjoint.le_bot ⟨hxker, x.property⟩
      simpa only [Submodule.mem_bot] using (Subtype.ext hz : x = 0)
    let f := LinearEquiv.ofBijective (-r)
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
    exact f.isUnit_det'
  · have hchar := congrArg (fun f : Module.End F V => f.charpoly) hd
    rw [LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap, LinearMap.charpoly_zero] at hchar
    rw [hchar, det_neg_eq_charpoly_coeff_zero]
    simpa only [zero_add] using
      (Polynomial.coeff_X_pow_mul r.charpoly (Module.finrank F d.ker) 0).symm

end SplitEndomorphism

/-- The differential with the identity in the torus direction and the negative
adjoint defect in the transverse direction has determinant `D_G(γ)`. -/
abbrev OrdinaryWeylDifferentialStatement : Prop :=
  ∀ {F : Type u} [Field F] {n : ℕ} (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ),
    let d := adjointDefect γ
    let P := d.ker.projection d.range (isCompl_ker_range_adjointDefect γ hγ)
    IsUnit (P - d).det ∧ (P - d).det = weylDiscriminant γ

theorem det_ordinaryWeylDifferential : OrdinaryWeylDifferentialStatement.{u} := by
  intro F _ n γ hγ
  have hdet :=
    det_projection_sub_of_isCompl (adjointDefect γ) (isCompl_ker_range_adjointDefect γ hγ)
  rw [finrank_ker_adjointDefect γ hγ] at hdet
  exact hdet

end Langlands.BaseChange
