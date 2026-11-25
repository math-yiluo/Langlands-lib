/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Triangularization of a single endomorphism

Over an algebraically closed field every endomorphism of a finite dimensional vector space
can be put in upper triangular form. Equivalently, it preserves a *complete flag*: an
increasing chain of subspaces starting at `⊥`, ending at `⊤`, whose `i`-th member has
dimension `i`, so that all graded pieces are one dimensional.

## Main results

- `Module.End.exists_complete_invariant_flag`: the existence of such a flag.
- `Module.End.exists_basis_isUpperTriangular_toMatrix`: the existence of a basis in which the
  matrix of the endomorphism is upper triangular.

## Implementation notes

The flag is indexed by `Fin (n + 1)`, `n = finrank K V`, rather than by `ℕ`, so that the
dimension condition pins it down completely. The endpoints `F 0 = ⊥` and
`F (Fin.last n) = ⊤` and the one-dimensionality of the successive quotients all follow
from the dimension condition, so they are not recorded separately.

Mathlib has the generalized eigenspace decomposition
`Module.End.iSup_maxGenEigenspace_eq_top` over an algebraically closed field, but no flag
statement; indeed `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` lists
triangularizability as a `TODO`.
-/

@[expose] public section

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An `f`-invariant proper subspace `W` of a finite dimensional vector space over an
algebraically closed field is contained in an `f`-invariant subspace of dimension one more:
add an eigenvector of the endomorphism induced by `f` on `V ⧸ W`. This is the inductive step
of the triangularization (blueprint: `lemma-filtrations-spectra`). -/
theorem exists_le_map_le_finrank_eq_succ [IsAlgClosed K] [FiniteDimensional K V] (f : End K V)
    {W : Submodule K V} (hW : W.map f ≤ W) (hne : W ≠ ⊤) :
    ∃ W' : Submodule K V, W ≤ W' ∧ W'.map f ≤ W' ∧
      Module.finrank K W' = Module.finrank K W + 1 := by
  have hf : W ≤ W.comap f := Submodule.map_le_iff_le_comap.mp hW
  have : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨μ, hμ⟩ := exists_eigenvalue (W.mapQ W f hf)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  obtain ⟨v, rfl⟩ := W.mkQ_surjective x
  have hv : v ∉ W := fun h ↦ hx.2 ((Submodule.Quotient.mk_eq_zero W).mpr h)
  have hv₀ : v ≠ 0 := by
    rintro rfl
    exact hv W.zero_mem
  have hfv : f v - μ • v ∈ W := by
    rw [← Submodule.Quotient.eq]
    simpa using hx.apply_eq_smul
  refine ⟨W ⊔ K ∙ v, le_sup_left, ?_, ?_⟩
  · refine Submodule.map_le_iff_le_comap.mpr (sup_le (hf.trans (Submodule.comap_mono le_sup_left))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_))
    rw [Submodule.mem_comap, ← sub_add_cancel (f v) (μ • v)]
    exact Submodule.add_mem_sup hfv (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  · have hdisj : W ⊓ K ∙ v = ⊥ := by
      rw [← disjoint_iff, Submodule.disjoint_span_singleton' hv₀]
      exact hv
    have := Submodule.finrank_sup_add_finrank_inf_eq W (K ∙ v)
    rw [hdisj, finrank_bot, finrank_span_singleton hv₀] at this
    omega

/-- An endomorphism `f` of a finite dimensional vector space `V` over an algebraically
closed field `K` admits a complete flag of invariant subspaces: a monotone family
`F : Fin (finrank K V + 1) → Submodule K V` with each `F i` mapped into itself by `f` and
`finrank K (F i) = i`. A basis adapted to such a flag puts `f` in upper triangular form,
with the eigenvalues of `f` on the diagonal (blueprint: `lemma-filtrations-spectra`,
`lemma-filtrations-spectra`). -/
theorem exists_complete_invariant_flag [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ∃ F : Fin (Module.finrank K V + 1) → Submodule K V,
      Monotone F ∧ (∀ i, (F i).map f ≤ F i) ∧ ∀ i, Module.finrank K (F i) = (i : ℕ) := by
  have key : ∀ k ≤ Module.finrank K V, ∃ F : ℕ → Submodule K V, (∀ i, F i ≤ F (i + 1)) ∧
      (∀ i, (F i).map f ≤ F i) ∧ ∀ i ≤ k, Module.finrank K (F i) = i := by
    intro k
    induction k with
    | zero => exact fun _ ↦ ⟨fun _ ↦ ⊥, fun _ ↦ le_rfl, fun _ ↦ by simp,
        fun i hi ↦ by simp [Nat.le_zero.mp hi]⟩
    | succ k ih =>
      intro hk
      obtain ⟨F, h₁, h₂, h₃⟩ := ih (by omega)
      have hne : F k ≠ ⊤ := fun h ↦ by
        have := h₃ k le_rfl
        rw [h, finrank_top] at this
        omega
      obtain ⟨W, hW₁, hW₂, hW₃⟩ := exists_le_map_le_finrank_eq_succ f (h₂ k) hne
      refine ⟨fun i ↦ if i ≤ k then F i else W, fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_⟩
      · dsimp only
        split_ifs with ha hb hb
        · exact h₁ i
        · obtain rfl : i = k := by omega
          exact hW₁
        · omega
        · exact le_rfl
      · dsimp only
        split_ifs
        exacts [h₂ i, hW₂]
      · dsimp only
        by_cases ha : i ≤ k
        · exact (congrArg (fun p : Submodule K V ↦ finrank K p) (ite_eq_left ha)).trans (h₃ i ha)
        · refine (congrArg (fun p : Submodule K V ↦ finrank K p) (ite_eq_right ha)).trans ?_
          rw [hW₃, h₃ k le_rfl]
          omega
  obtain ⟨F, h₁, h₂, h₃⟩ := key _ le_rfl
  exact ⟨fun i ↦ F i, fun _ _ hij ↦ monotone_nat_of_le_succ h₁ hij, fun i ↦ h₂ i,
    fun i ↦ h₃ i (Nat.lt_succ_iff.mp i.2)⟩

/-- An endomorphism `f` of a finite dimensional vector space over an algebraically closed field
has an upper triangular matrix in a suitable basis: pick `b i` in the `(i + 1)`-st member of an
invariant complete flag but not in the `i`-th (`Module.End.exists_complete_invariant_flag`). -/
theorem exists_basis_isUpperTriangular_toMatrix [IsAlgClosed K] [FiniteDimensional K V]
    (f : End K V) : ∃ b : Basis (Fin (finrank K V)) K V,
      (LinearMap.toMatrix b b f).IsUpperTriangular := by
  set n := finrank K V
  obtain ⟨F, hmono, hinv, hdim⟩ := exists_complete_invariant_flag f
  have hlt : ∀ i : Fin n, ∃ v ∈ F i.succ, v ∉ F i.castSucc := fun i ↦
    IsConcreteLE.exists_of_lt <| lt_of_le_of_ne (hmono (Fin.castSucc_le_succ i)) fun h ↦ by
      have := congrArg (fun p : Submodule K V ↦ finrank K p) h
      simp only [hdim, Fin.val_castSucc, Fin.val_succ] at this
      omega
  choose v hv hv' using hlt
  have key : ∀ k (hk : k ≤ n),
      Submodule.span K (v '' {i | (i : ℕ) < k}) = F ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have : finrank K (F ⟨0, Nat.lt_succ_of_le hk⟩) = 0 := hdim _
      simpa using (Submodule.finrank_eq_zero.mp this).symm
    | succ k ih =>
      intro hk
      set i₀ : Fin n := ⟨k, by omega⟩ with hi₀
      have hset : {i : Fin n | (i : ℕ) < k + 1} =
          insert i₀ {i : Fin n | (i : ℕ) < k} := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, hi₀, Fin.ext_iff]
        omega
      rw [hset, Set.image_insert_eq, Submodule.span_insert, ih (by omega)]
      have hle : K ∙ v i₀ ⊔ F ⟨k, by omega⟩ ≤ F ⟨k + 1, by omega⟩ :=
        sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hv i₀))
          (hmono (Fin.mk_le_mk.mpr (by omega)))
      refine Submodule.eq_of_le_of_finrank_le hle ?_
      have hlt : F ⟨k, by omega⟩ < K ∙ v i₀ ⊔ F ⟨k, by omega⟩ :=
        lt_of_le_of_ne le_sup_right fun h ↦ hv' i₀ (show v i₀ ∈ F ⟨k, by omega⟩ by
          rw [h]
          exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
      have := Submodule.finrank_lt_finrank_of_lt hlt
      have h1 := hdim ⟨k, by omega⟩
      have h2 := hdim ⟨k + 1, by omega⟩
      simp only at h1 h2
      omega
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    have h := key n le_rfl
    have : {i : Fin n | (i : ℕ) < n} = Set.univ := Set.eq_univ_of_forall fun i ↦ i.2
    rw [this, Set.image_univ] at h
    rw [h]
    apply Submodule.eq_top_of_finrank_eq
    rw [hdim]
  let b := basisOfTopLeSpanOfCardEqFinrank v htop.ge (Fintype.card_fin n)
  refine ⟨b, fun i j hij ↦ ?_⟩
  change j < i at hij
  have hb : ⇑b = v := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  have hmem : f (b j) ∈ Submodule.span K (b '' {i | (i : ℕ) < j + 1}) := by
    rw [hb, key _ (by omega)]
    exact hinv _ (Submodule.mem_map_of_mem (hv j))
  rw [Basis.mem_span_image] at hmem
  rw [LinearMap.toMatrix_apply]
  by_contra hne
  have := hmem (Finsupp.mem_support_iff.mpr hne)
  simp only [Set.mem_ofPred_eq] at this
  exact absurd hij (by rw [Fin.lt_def]; omega)

end Module.End
