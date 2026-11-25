/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Continuous-field matrix elimination

The constant-rank argument for locally finite functions in
`WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix` applies directly to continuous functions
into a normed field. The splitting `FiniteIndexSplitting.sumComplEquiv` of a finite index set
along an injection is the coefficient-independent part of that file.
-/

@[expose] public section

universe u v w

namespace FiniteIndexSplitting

variable {κ : Type*} [DecidableEq κ]

/-- The splitting `κ ≃ Fin r ⊕ (κ ∖ range ρ)` along an injection `ρ : Fin r → κ`. -/
noncomputable def sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} :=
  (Equiv.sumCompl (· ∈ Set.range ρ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective ρ hρ).symm (Equiv.refl _))

@[simp]
lemma sumComplEquiv_symm_inl {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) (a : Fin r) :
    (sumComplEquiv ρ hρ).symm (Sum.inl a) = ρ a := by
  simp [sumComplEquiv]

end FiniteIndexSplitting

namespace AlgebraicGeometry.ProEtale

variable {E : Type u} [NormedField E] {T : Type v} [TopologicalSpace T]

/-- Evaluation of continuous field-valued functions.
Source: pointwise ring operations on continuous functions
(auxiliary; not a blueprint node). -/
abbrev continuousFieldEval (t : T) : C(T, E) →+* E :=
  (ContinuousMap.evalAlgHom ℤ E t).toRingHom

private lemma isUnit_continuousField {S : Type*} [TopologicalSpace S]
    (f : C(S, E)) (hf : ∀ s, f s ≠ 0) : IsUnit f := by
  let g : C(S, E) := ⟨fun s ↦ (f s)⁻¹, f.continuous.inv₀ hf⟩
  refine ⟨⟨f, g, ?_, ?_⟩, rfl⟩ <;> ext s
  · exact mul_inv_cancel₀ (hf s)
  · exact inv_mul_cancel₀ (hf s)

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

/-- The splitting `κ ≃ Fin r ⊕ (κ ∖ range ρ)` along an injection `ρ : Fin r → κ`. -/
noncomputable abbrev sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} := FiniteIndexSplitting.sumComplEquiv ρ hρ

/-- Pulled back to a neighbourhood of a point, a matrix of continuous functions
of constant rank `r` is equivalent to the matrix `[[1, 0], [0, 0]]` with an `r × r` identity
block.
Source: the Gaussian elimination step of the rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
Proof: choose a nonzero maximal minor at the point and restrict to its nonvanishing
open locus. Its inverse matrix has continuous entries. The Schur complement is zero
by the pointwise rank bound and injectivity of evaluation of continuous functions.
The two invertible block operations yield the asserted identity, including rank zero. -/
lemma continuousField_exists_isOpen_eq_mul (M : Matrix κ ι (C(T, E))) (r : ℕ)
    (hr : ∀ t, (M.map (continuousFieldEval t)).rank = r) (t₀ : T) :
    ∃ (U : Set T) (ρ : Fin r → κ) (γ : Fin r → ι) (hρ : Function.Injective ρ)
      (hγ : Function.Injective γ), IsOpen U ∧ t₀ ∈ U ∧
      ∀ {T' : Type w} [TopologicalSpace T'] (g : C(T', T)), Set.range g ⊆ U →
        ∃ (P : Matrix κ κ (C(T', E)))
        (Q : Matrix ι ι (C(T', E))), IsUnit P.det ∧ IsUnit Q.det ∧
        M.map ((ContinuousMap.compRightAlgHom ℤ E g)) = P * ((Matrix.fromBlocks 1 0 0 0 :
          Matrix (Fin r ⊕ {i // i ∉ Set.range ρ}) (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
            (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q := by
  obtain ⟨ρ, γ, h⟩ := (M.le_rank_map_iff (continuousFieldEval t₀) r).1 (hr t₀).ge
  have hρ : Function.Injective ρ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_row_eq hne (by ext; simp [hab]), map_zero])
  have hγ : Function.Injective γ := fun a b hab ↦ by
    by_contra hne
    exact h (by rw [Matrix.det_zero_of_column_eq hne (by intro; simp [hab]), map_zero])
  let δ := (M.submatrix ρ γ).det
  refine ⟨{t | δ t ≠ 0}, ρ, γ, hρ, hγ, isOpen_compl_singleton.preimage δ.continuous, h,
    fun {T'} _ g hg ↦ ?_⟩
  let M' := M.map ((ContinuousMap.compRightAlgHom ℤ E g))
  let N := M'.reindex (sumComplEquiv ρ hρ) (sumComplEquiv γ hγ)
  have hN : N = Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks N).symm
  have hB : N.toBlocks₁₁ = (M.submatrix ρ γ).map ((ContinuousMap.compRightAlgHom ℤ E g)) := by
    ext a b
    simp [N, M', Matrix.toBlocks₁₁]
  have hBu : IsUnit N.toBlocks₁₁.det := by
    rw [hB]
    erw [← RingHom.map_det ((ContinuousMap.compRightAlgHom ℤ E g)).toRingHom]
    refine isUnit_continuousField _ fun t' ↦ ?_
    exact hg ⟨t', rfl⟩
  let := N.toBlocks₁₁.invertibleOfIsUnitDet hBu
  have hS := Matrix.schur_eq_zero_of_rank_le (fun t' : T' ↦ continuousFieldEval t')
    (fun x hx ↦ ContinuousMap.ext hx) N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁
    N.toBlocks₂₂ (fun t' ↦ ?_)
  · rw [Matrix.invOf_eq_nonsing_inv] at hS
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := Matrix.exists_eq_mul_fromBlocks_one_zero _ _ _ _ hBu hS
    refine ⟨P.reindex (sumComplEquiv ρ hρ).symm (sumComplEquiv ρ hρ).symm,
      Q.reindex (sumComplEquiv γ hγ).symm (sumComplEquiv γ hγ).symm, by simpa using hP,
      by simpa using hQ, ?_⟩
    have hM' : M' = N.reindex (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm := by simp [N]
    change M' = _
    rw [hM', hN, hPQ]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  · rw [← hN]
    have : N.map (continuousFieldEval t') =
        (M.map (continuousFieldEval (g t'))).reindex (sumComplEquiv ρ hρ)
          (sumComplEquiv γ hγ) := by
      ext a b
      rfl
    rw [this, Matrix.rank_reindex, hr, Fintype.card_fin]

/-- The same local matrix normal form when the rank is locally constant. -/
lemma continuousField_exists_isOpen_eq_mul_of_locallyConstant
    (M : Matrix κ ι (C(T, E)))
    (hr : IsLocallyConstant (fun t ↦ (M.map (continuousFieldEval t)).rank)) (t₀ : T) :
    ∃ (r : ℕ) (U : Set T) (ρ : Fin r → κ) (γ : Fin r → ι)
      (hρ : Function.Injective ρ) (hγ : Function.Injective γ), IsOpen U ∧ t₀ ∈ U ∧
      ∀ {T' : Type w} [TopologicalSpace T'] (g : C(T', T)), Set.range g ⊆ U →
        ∃ (P : Matrix κ κ (C(T', E))) (Q : Matrix ι ι (C(T', E))),
          IsUnit P.det ∧ IsUnit Q.det ∧
          M.map (ContinuousMap.compRightAlgHom ℤ E g) = P *
            ((Matrix.fromBlocks 1 0 0 0 :
              Matrix (Fin r ⊕ {i // i ∉ Set.range ρ})
                (Fin r ⊕ {j // j ∉ Set.range γ}) _).reindex
                  (sumComplEquiv ρ hρ).symm (sumComplEquiv γ hγ).symm) * Q := by
  obtain ⟨S, hS, ht, hconst⟩ := hr.exists_open t₀
  let inc : C(S, T) := ⟨Subtype.val, continuous_subtype_val⟩
  let M' := M.map (ContinuousMap.compRightAlgHom ℤ E inc)
  obtain ⟨U, ρ, γ, hρ, hγ, hU, htU, h⟩ := continuousField_exists_isOpen_eq_mul M'
    ((M.map (continuousFieldEval t₀)).rank) (fun t ↦ hconst t t.2) ⟨t₀, ht⟩
  refine ⟨_, Subtype.val '' U, ρ, γ, hρ, hγ,
    hS.isOpenMap_subtype_val U hU, ⟨⟨t₀, ht⟩, htU, rfl⟩, ?_⟩
  intro T' _ g hg
  have hmem (t : T') : g t ∈ S := by
    obtain ⟨s, _, hs⟩ := hg ⟨t, rfl⟩
    exact hs ▸ s.2
  let g' : C(T', S) := ⟨fun t ↦ ⟨g t, hmem t⟩,
    g.continuous.subtype_mk (fun t ↦ hmem t)⟩
  have hg' : Set.range g' ⊆ U := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, hs, hst⟩ := hg ⟨t, rfl⟩
    have heq : s = g' t := Subtype.ext hst
    exact heq ▸ hs
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := h g' hg'
  refine ⟨P, Q, hP, hQ, ?_⟩
  convert hPQ using 1
  ext i j t
  rfl

end AlgebraicGeometry.ProEtale
