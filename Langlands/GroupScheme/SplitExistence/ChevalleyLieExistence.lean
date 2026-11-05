import Langlands.GroupScheme.SplitExistence.ShortRootRep
import Langlands.GroupScheme.SplitExistence.ChevalleyLieConstruction

/-!
# Existence of integral Chevalley data

For a reduced root datum `P` with base `b` and a finite generating family `gen` of the character
lattice `X`, the short-root module (basis indexed by the simple roots, the short roots and the
minimal-norm weights of the cosets `gen w + ℤΦ`), reindexed by `Fin n`, together with the
representations `simpleRep` of the simple roots, is integral `SL₂`-data for the simple roots
(`shortRootData`). Combined with the construction of the root operators for all roots, this gives
integral Chevalley data for every reduced root datum whose character lattice is finitely
generated (`nonempty_chevalleyLieData`).
-/

noncomputable section

universe u

open Matrix RootPairing

namespace Langlands.GroupScheme.SplitExistence

section Module

variable {J X Y : Type u} [Fintype J] [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}
  [P.IsReduced] {b : P.Base} {r : ℕ} {gen : Fin r → X}

open Classical

/-! ### The size and the weights of the short-root module -/

variable (gen) in
/-- The short-root module has at least three basis vectors as soon as there is a simple root:
`u_i`, and `v_β`, `v_{-β}` for a short root `β`. -/
theorem three_le_card_idx (i : b.support) : 3 ≤ Fintype.card (Idx P b gen) := by
  obtain ⟨β, hβ⟩ : ∃ β, IsShortRoot P β := by
    by_cases hi : IsShortRoot P i
    · exact ⟨i, hi⟩
    · obtain ⟨β, hβ, -⟩ := exists_isShortRoot_pairing_eq_neg_one (i : J) hi
      exact ⟨β, hβ⟩
  let γ : ShortIdx P := ⟨β, hβ⟩
  have hne : shRefl (P := P) β γ ≠ γ := by
    intro h
    have h' : P.root (P.reflectionPerm β β) = P.root β :=
      congrArg (fun δ : ShortIdx P => P.root δ) h
    rw [root_reflectionPerm_self] at h'
    exact root_ne_neg_self β h'.symm
  have h3 : ({.inl (.inl i), .inl (.inr γ), .inl (.inr (shRefl β γ))} :
      Finset (Idx P b gen)).card = 3 :=
    Finset.card_eq_three.2 ⟨_, _, _, by simp, by simp,
      fun h => hne (Sum.inr_injective (Sum.inl_injective h)).symm, rfl⟩
  exact h3 ▸ Finset.card_le_univ _

/-- Every root is an integral combination of the weights of the short-root module: a root that
is not short is the difference `α_{s_x β} - α_β` of two short roots. -/
theorem root_mem_span_range_idxWt (j : J) :
    P.root j ∈ Submodule.span ℤ (Set.range (idxWt P b gen)) := by
  by_cases hj : IsShortRoot P j
  · exact Submodule.subset_span ⟨.inl (.inr ⟨j, hj⟩), rfl⟩
  · obtain ⟨β, hβ, hβj⟩ := exists_isShortRoot_pairing_eq_neg_one j hj
    have h : P.root j = P.root (P.reflectionPerm j β) - P.root β := by
      rw [root_reflectionPerm, reflection_apply_root, hβj, neg_smul, one_smul]
      abel
    rw [h]
    exact Submodule.sub_mem _
      (Submodule.subset_span ⟨.inl (.inr ⟨_, hβ.reflectionPerm j⟩), rfl⟩)
      (Submodule.subset_span ⟨.inl (.inr ⟨β, hβ⟩), rfl⟩)

/-- The weights of the short-root module span `X` when `gen` does: every `gen w` differs from a
minimal-norm weight of its coset by an element of the root lattice. -/
theorem span_range_idxWt (hgen : Submodule.span ℤ (Set.range gen) = ⊤) :
    Submodule.span ℤ (Set.range (idxWt P b gen)) = ⊤ := by
  rw [eq_top_iff, ← hgen, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  obtain ⟨ν, hν⟩ := minimalWeights_nonempty (P := P) (gen w)
  have hroot : P.rootSpan ℤ ≤ Submodule.span ℤ (Set.range (idxWt P b gen)) := by
    apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    exact root_mem_span_range_idxWt j
  have h1 : ν ∈ Submodule.span ℤ (Set.range (idxWt P b gen)) :=
    Submodule.subset_span ⟨.inr ⟨ν, w, hν⟩, rfl⟩
  have h2 := hroot hν.1
  rw [show gen w = ν - (ν - gen w) by abel]
  exact Submodule.sub_mem _ h1 h2

theorem closure_range_idxWt_comp (hgen : Submodule.span ℤ (Set.range gen) = ⊤) :
    AddSubgroup.closure
      (Set.range (idxWt P b gen ∘ (Fintype.equivFin (Idx P b gen)).symm)) = ⊤ := by
  rw [(Fintype.equivFin _).symm.surjective.range_comp, ← Submodule.span_int_eq_addSubgroupClosure,
    span_range_idxWt hgen, Submodule.top_toAddSubgroup]

/-! ### The representations of the simple roots on `ℤ^n` -/

variable (b gen) in
/-- The representation `simpleRep i` of the simple root `α_i`, reindexed by
`Fin (Fintype.card (Idx P b gen))`. -/
def finRep (i : b.support) :
    SL2Rep.{0, u, u} (Fin (Fintype.card (Idx P b gen)))
      (idxWt P b gen ∘ (Fintype.equivFin (Idx P b gen)).symm) (P.root i) (corootHom P i) :=
  (simpleRep b gen i).reindex (Fintype.equivFin _)

omit [P.IsReduced] in
theorem finRep_E_one (i : b.support) :
    (finRep b gen i).E 1 =
      (raiseMat P b gen i).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm := by
  rw [finRep, SL2Rep.reindex_E, simpleRep_E_one]

omit [P.IsReduced] in
theorem finRep_F_one (i : b.support) :
    (finRep b gen i).F 1 =
      (lowerMat P b gen i).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm := by
  rw [finRep, SL2Rep.reindex_F, simpleRep_F_one]

theorem finRep_E_one_map_ne_zero (i : b.support) (p : ℕ) (hp : p.Prime) :
    ((finRep b gen i).E 1).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  have := Fact.mk hp
  obtain ⟨c, hc⟩ := exists_raiseCoeff_eq_one (gen := gen) i
  rw [finRep_E_one, raiseMat]
  exact submatrix_map_ne_zero _ (colMat_map_ne_zero hc p)

theorem finRep_F_one_map_ne_zero (i : b.support) (p : ℕ) (hp : p.Prime) :
    ((finRep b gen i).F 1).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  have := Fact.mk hp
  obtain ⟨c, hc⟩ := exists_lowerCoeff_eq_one (gen := gen) i
  rw [finRep_F_one, lowerMat]
  exact submatrix_map_ne_zero _ (colMat_map_ne_zero hc p)

theorem finRep_E_F_comm {i i' : b.support} (h : i ≠ i') :
    (finRep b gen i).E 1 * (finRep b gen i').F 1 =
      (finRep b gen i').F 1 * (finRep b gen i).E 1 := by
  rw [finRep_E_one, finRep_F_one, submatrix_mul_equiv, submatrix_mul_equiv,
    raiseMat_mul_lowerMat_comm h]

/-! ### The integral `SL₂`-data -/

variable (b gen) in
/-- The integral `SL₂`-data of the short-root module, for a generating family `gen` of `X`. -/
def shortRootData (hgen : Submodule.span ℤ (Set.range gen) = ⊤) : SimpleRootData P b where
  ℓ := posCorootSum b
  ℓ_pos _ hi := posCorootSum_pos b hi
  n := Fintype.card (Idx P b gen)
  wt := idxWt P b gen ∘ (Fintype.equivFin (Idx P b gen)).symm
  closure_range_wt := closure_range_idxWt_comp hgen
  E i k := (finRep b gen i).E k
  F i k := (finRep b gen i).F k
  E_zero i := (finRep b gen i).E_zero
  F_zero i := (finRep b gen i).F_zero
  E_mul i := (finRep b gen i).E_mul
  F_mul i := (finRep b gen i).F_mul
  E_eq_zero i k hk :=
    (finRep b gen i).E_eq_zero k (by have := three_le_card_idx gen i; omega)
  F_eq_zero i k hk :=
    (finRep b gen i).F_eq_zero k (by have := three_le_card_idx gen i; omega)
  E_weight i := (finRep b gen i).E_weight
  F_weight i := (finRep b gen i).F_weight
  E_one_map_ne_zero i p hp := finRep_E_one_map_ne_zero i p hp
  F_one_map_ne_zero i p hp := finRep_F_one_map_ne_zero i p hp
  φ i R _ := (finRep b gen i).hom R
  φ_natural i R S _ _ f g := (finRep b gen i).rep_map R S f g
  φ_upper i R _ s :=
    (finRep b gen i).rep_upper R _ (by have := three_le_card_idx gen i; omega) s
  φ_lower i R _ s :=
    (finRep b gen i).rep_lower R _ (by have := three_le_card_idx gen i; omega) s
  φ_diag i R _ t := (finRep b gen i).rep_diag R t
  weyl_weight i R _ c d h := by
    rw [reflection_apply]
    exact (finRep b gen i).rep_weyl R c d h
  E_F_same i := (finRep b gen i).E_one_mul_F_one_sub
  E_F_comm _ _ h := finRep_E_F_comm h

end Module

/-- Integral `SL₂`-data for the simple roots exist for every reduced root datum with finitely
many roots and finitely generated character lattice. -/
theorem nonempty_simpleRootData {J X Y : Type u} [Finite J] [AddCommGroup X] [AddCommGroup Y]
    [Module.Finite ℤ X] (P : RootDatum J X Y) [P.IsReduced] (b : P.Base) :
    Nonempty (SimpleRootData P b) := by
  cases nonempty_fintype J
  obtain ⟨r, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := X)
  exact ⟨shortRootData b gen hgen⟩

/-- **Existence of integral Chevalley data** for every reduced root datum with finitely many
roots and finitely generated character lattice. -/
theorem nonempty_chevalleyLieData {J X Y : Type u} [Finite J] [AddCommGroup X] [AddCommGroup Y]
    [Module.Finite ℤ X] (P : RootDatum J X Y) [P.IsReduced] (b : P.Base) :
    Nonempty (ChevalleyLieData P b) :=
  nonempty_chevalleyLieData_of_simpleRootData (nonempty_simpleRootData P b)

end Langlands.GroupScheme.SplitExistence
