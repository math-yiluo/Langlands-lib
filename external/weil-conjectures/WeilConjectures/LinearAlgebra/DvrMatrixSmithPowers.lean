/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Scalar Smith matrices with uniformizer powers -/

@[expose] public section

universe u

namespace Matrix

/-- A rectangular matrix over a DVR has a two-sided Smith presentation by sorted
uniformizer powers. The number of nonzero entries is its module rank.

Source: Mathlib's `Submodule.smithNormalForm` and
`Submodule.exists_smith_normal_form_of_le`; Stacks Project, Algebra, Tag 00PD
for the DVR characterization. Agent passage to a rectangular matrix.
(auxiliary; not a blueprint node)

Proof: Apply scalar Smith form to the image of the matrix map in the finite free
codomain. Its diagonal coefficients are nonzero, since the image basis is linearly
independent. The image is free. Lift its basis to the source to split the surjection
onto the image. The kernel is a finite free submodule over the PID, so a kernel basis
and the lifted image basis give a source basis. In these bases the matrix is rectangular
diagonal. Every nonzero coefficient is a unit times a unique nonnegative power of the
uniformizer. Absorb the units into the codomain basis and simultaneously permute the
first image coordinates in source and target to sort the exponents. The number of
image basis vectors equals the rank of the matrix and is bounded by both dimensions.
With empty image or either matrix dimension zero the same construction uses empty
bases and the zero diagonal. -/
theorem exists_smith_pow {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A)
    (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (m n : ℕ)
    (F : Matrix (Fin n) (Fin m) A) :
    ∃ (L : GeneralLinearGroup (Fin n) A) (R : GeneralLinearGroup (Fin m) A)
      (r : ℕ) (_hr : r ≤ min m n) (e : Fin r → ℕ) (D : Matrix (Fin n) (Fin m) A),
      Monotone e ∧
      (∀ (i : Fin n) (j : Fin m),
        D i j = if h : i.val = j.val ∧ i.val < r then π ^ e ⟨i.val, h.2⟩ else 0) ∧
      r = F.rank ∧ (L : Matrix (Fin n) (Fin n) A) * F *
        (R : Matrix (Fin m) (Fin m) A) = D := by
  classical
  let f := F.mulVecLin
  obtain ⟨r, snf⟩ := (LinearMap.range f).smithNormalForm (Pi.basisFun A (Fin n))
  have hrank : r = F.rank := by
    change r = Module.finrank A (LinearMap.range f)
    exact by simpa using (Module.finrank_eq_card_basis snf.bN).symm
  have hrn : r ≤ n := by
    simpa using Fintype.card_le_of_injective snf.f snf.f.injective
  have hrm : r ≤ m := hrank ▸ F.rank_le_width
  have ha (i : Fin r) : snf.a i ≠ 0 := by
    intro h
    have hb := snf.snf i
    rw [h, zero_smul] at hb
    exact snf.bN.ne_zero i (Subtype.ext hb)
  have hπi := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  choose e u hu using fun i ↦ IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha i) hπi
  let σ := Tuple.sort e
  let es : Fin r → ℕ := e ∘ σ
  have hes : Monotone es := Tuple.monotone_sort e
  let bN := snf.bN.reindex σ.symm
  obtain ⟨k, bK⟩ := (LinearMap.ker f).basisOfPid (Pi.basisFun A (Fin m))
  let bQ := bN.map f.quotKerEquivRange.symm
  let bS₀ := bK.sumQuot bQ
  have hsize : k + r = m := by
    have h := Module.finrank_eq_card_basis bS₀
    simpa using h.symm
  have hfS (i : Fin r) : f (bS₀ (Sum.inr i)) = (bN i : Fin n → A) := by
    have h := bK.sumQuot_inr bQ i
    have h' := congrArg f.quotKerEquivRange h
    exact congrArg Subtype.val (h'.trans (by simp [bQ]))
  have hfK (i : Fin k) : f (bS₀ (Sum.inl i)) = 0 := by
    simpa only [bS₀, Module.Basis.sumQuot_inl] using (LinearMap.mem_ker.mp (bK i).property)
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin r ↦ Fin.castLE hrn i) (fun i ↦ snf.f (σ i))
    (Fin.castLE_injective hrn) (snf.f.injective.comp σ.injective)
  let w : Fin n → Aˣ := fun i ↦ if hi : i.val < r then u (σ ⟨i.val, hi⟩) else 1
  let bT := (snf.bM.reindex ρ.symm).unitsSMul w
  have hbT (i : Fin r) :
      bT (Fin.castLE hrn i) = (u (σ i) : A) • snf.bM (snf.f (σ i)) := by
    simp only [bT, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
      Equiv.symm_symm, hρ, w, Fin.val_castLE, dite_eq_left i.isLt]
    rfl
  have himage (i : Fin r) :
      (bN i : Fin n → A) = π ^ es i • bT (Fin.castLE hrn i) := by
    rw [hbT]
    simp only [bN, Module.Basis.reindex_apply, Equiv.symm_symm]
    rw [snf.snf, hu]
    simp only [es, Function.comp_apply, smul_smul]
    rw [mul_comm]
  have hsize' : r + k = m := by omega
  let index : Fin k ⊕ Fin r ≃ Fin m :=
    (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr hsize'))
  let bSrc := bS₀.reindex index
  have hSrc (i : Fin r) : bSrc (Fin.castLE hrm i) = bS₀ (Sum.inr i) := by
    simp only [bSrc, Module.Basis.reindex_apply]
    apply congrArg bS₀
    apply index.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl
  have hSrcK (i : Fin k) :
      bSrc (Fin.cast hsize' (Fin.natAdd r i)) = bS₀ (Sum.inl i) := by
    simp only [bSrc, Module.Basis.reindex_apply]
    apply congrArg bS₀
    apply index.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl
  let L := GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv bT.equivFun)
  let R := GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv bSrc.equivFun.symm)
  let D := (L : Matrix (Fin n) (Fin n) A) * F * (R : Matrix (Fin m) (Fin m) A)
  refine ⟨L, R, r, le_min hrm hrn, es, D, hes, ?_, hrank, rfl⟩
  have hD (i : Fin n) (j : Fin m) : D i j = bT.repr (f (bSrc j)) i := by
    change ((L : Matrix (Fin n) (Fin n) A) * F *
      (R : Matrix (Fin m) (Fin m) A)) i j = _
    have hL : (L : Matrix (Fin n) (Fin n) A).mulVecLin = bT.equivFun.toLinearMap := by
      exact congrArg Units.val (GeneralLinearGroup.toLin.apply_symm_apply _)
    have hR : (R : Matrix (Fin m) (Fin m) A).mulVecLin =
        bSrc.equivFun.symm.toLinearMap := by
      exact congrArg Units.val (GeneralLinearGroup.toLin.apply_symm_apply _)
    have hvec : ((L : Matrix (Fin n) (Fin n) A) * F *
        (R : Matrix (Fin m) (Fin m) A)).mulVecLin =
        bT.equivFun.toLinearMap.comp (f.comp bSrc.equivFun.symm.toLinearMap) := by
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, hL, hR]
      rfl
    have hv := LinearMap.congr_fun hvec (Pi.single j 1)
    have hb : bSrc.equivFun.symm (Pi.single j 1) = bSrc j := by
      simp [Module.Basis.equivFun_symm_apply]
    have hv' := congrFun hv i
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, hb, Module.Basis.equivFun_apply] using hv'
  intro i j
  rw [hD]
  by_cases hj : j.val < r
  · have hj' : j = Fin.castLE hrm ⟨j.val, hj⟩ := rfl
    have hf : f (bSrc j) = π ^ es ⟨j.val, hj⟩ • bT (Fin.castLE hrn ⟨j.val, hj⟩) := by
      calc
        f (bSrc j) = f (bSrc (Fin.castLE hrm ⟨j.val, hj⟩)) :=
          congrArg (fun a ↦ f (bSrc a)) hj'
        _ = _ := by rw [hSrc, hfS, himage]
    rw [hf, map_smul, Module.Basis.repr_self]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hi : i.val = j.val
    · have hij : Fin.castLE hrn ⟨j.val, hj⟩ = i := Fin.ext hi.symm
      rw [ite_eq_left hij, mul_one, dite_eq_left ⟨hi, by omega⟩]
      congr 2
      exact Fin.ext hi.symm
    · have hij : Fin.castLE hrn ⟨j.val, hj⟩ ≠ i := by
        intro h
        exact hi (congrArg Fin.val h).symm
      rw [ite_eq_right hij, mul_zero, dite_eq_right (fun h ↦ hi h.1)]
  · obtain ⟨a, ha⟩ : ∃ a : Fin k, j = Fin.cast hsize' (Fin.natAdd r a) := by
      refine ⟨⟨j.val - r, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega
    rw [ha, hSrcK, hfK, map_zero]
    simp only [Finsupp.zero_apply, Fin.val_cast, Fin.val_natAdd]
    split_ifs with h
    · omega
    · rfl

end Matrix
