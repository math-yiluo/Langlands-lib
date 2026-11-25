/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Engel
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Engel's theorem for Lie algebras of nilpotent endomorphisms

This file records the classical matrix form of Engel's theorem: a Lie algebra of nilpotent
endomorphisms of a nonzero finite-dimensional vector space has a common null vector and is
nilpotent, and there is a basis in which all its elements are strictly upper triangular. It is a
direct consequence of Mathlib's `LieModule.isNilpotent_iff_forall'`.

## Main declarations

* `LieSubalgebra.exists_forall_apply_eq_zero_and_isNilpotent`: Engel's matrix lemma.
* `LieSubalgebra.exists_basis_toMatrix_apply_eq_zero_of_le`: a basis in which all elements are
  strictly upper triangular.

## Blueprint

`LieSubalgebra.exists_forall_apply_eq_zero_and_isNilpotent` implements `lemma-engel-s-theorem`.
-/

@[expose] public section

open LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

/-- **Engel's matrix lemma.** Let `A` be a Lie algebra of endomorphisms of a nonzero
finite-dimensional vector space `M`, all of whose elements are nilpotent. Then some nonzero vector
of `M` is killed by every element of `A`, and `A` is a nilpotent Lie algebra.
(blueprint: `lemma-engel-s-theorem`) -/
theorem exists_forall_apply_eq_zero_and_isNilpotent [Nontrivial M]
    (A : LieSubalgebra k (Module.End k M)) (hA : ∀ X ∈ A, IsNilpotent X) :
    (∃ v : M, v ≠ 0 ∧ ∀ X ∈ A, X v = 0) ∧ LieRing.IsNilpotent A := by
  have hM : LieModule.IsNilpotent A M :=
    (LieModule.isNilpotent_iff_forall' (R := k)).mpr fun X ↦ hA X X.2
  refine ⟨?_, (LieAlgebra.isNilpotent_iff_forall (R := k)).mpr fun X ↦
    LieAlgebra.isNilpotent_ad_of_isNilpotent (hA X X.2)⟩
  have := nontrivial_max_triv_of_isNilpotent k A M
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : maxTrivSubmodule k A M)
  refine ⟨v, fun h ↦ hv0 (Subtype.ext h), fun X hX ↦ ?_⟩
  exact (mem_maxTrivSubmodule k A M v).mp hv ⟨X, hX⟩

/-- **Engel's theorem, triangular form.** If `A` is a Lie algebra of nilpotent endomorphisms of a
finite-dimensional vector space `M`, then there is a basis of `M` in which every element of `A`
is strictly upper triangular. -/
theorem exists_basis_toMatrix_apply_eq_zero_of_le (A : LieSubalgebra k (Module.End k M))
    (hA : ∀ X ∈ A, IsNilpotent X) :
    ∃ b : Module.Basis (Fin (Module.finrank k M)) k M,
      ∀ X ∈ A, ∀ i j, j ≤ i → LinearMap.toMatrix b b X i j = 0 := by
  have hM : LieModule.IsNilpotent A M :=
    (LieModule.isNilpotent_iff_forall' (R := k)).mpr fun X ↦ hA X X.2
  obtain ⟨l, hl⟩ := (LieModule.isNilpotent_iff_exists_ucs_eq_top k (L := A) (M := M)).mp hM
  -- Every proper subspace `W` misses a vector that all elements of `A` send into `W`: otherwise
  -- `W` would contain the whole upper central series of `M`.
  have step (W : Submodule k M) (hW : W ≠ ⊤) : ∃ u ∉ W, ∀ X ∈ A, X u ∈ W := by
    by_contra! h
    have hucs (i : ℕ) : ((⊥ : LieSubmodule k A M).ucs i : Submodule k M) ≤ W := by
      induction i with
      | zero => simp
      | succ i ih =>
        intro u hu
        rw [LieSubmodule.mem_toSubmodule, LieSubmodule.ucs_succ,
          LieSubmodule.mem_normalizer] at hu
        by_contra hu'
        obtain ⟨X, hX, hXu⟩ := h u hu'
        exact hXu (ih (hu ⟨X, hX⟩))
    exact hW (eq_top_iff.mpr (by simpa [hl] using hucs l))
  have key (m : ℕ) (hm : m ≤ Module.finrank k M) :
      ∃ v : Fin m → M, LinearIndependent k v ∧
        ∀ X ∈ A, ∀ j, X (v j) ∈ Submodule.span k (v '' {i | i < j}) := by
    induction m with
    | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun _ _ j ↦ j.elim0⟩
    | succ m ih =>
      obtain ⟨v, hv, hvA⟩ := ih (by omega)
      have hW : Submodule.span k (Set.range v) ≠ ⊤ := fun h ↦ by
        have := finrank_span_eq_card hv
        rw [h, finrank_top, Fintype.card_fin] at this
        omega
      obtain ⟨u, hu, huA⟩ := step _ hW
      refine ⟨Fin.snoc v u, linearIndependent_finSnoc.mpr ⟨hv, hu⟩, fun X hX j ↦ ?_⟩
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        refine Submodule.span_mono ?_ (huA X hX)
        rintro _ ⟨i, rfl⟩
        exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩
      | cast j =>
        rw [Fin.snoc_castSucc]
        refine Submodule.span_mono ?_ (hvA X hX j)
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨i.castSucc, Fin.castSucc_lt_castSucc_iff.mpr hi, by simp⟩
  obtain ⟨v, hv, hvA⟩ := key _ le_rfl
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv (Fintype.card_fin _)
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  refine ⟨b, fun X hX i j hij ↦ ?_⟩
  have hmem := hvA X hX j
  rw [← hb, Module.Basis.mem_span_image] at hmem
  rw [LinearMap.toMatrix_apply]
  by_contra hne
  exact not_lt.mpr hij (hmem (Finsupp.mem_support_iff.mpr hne))

end LieSubalgebra
