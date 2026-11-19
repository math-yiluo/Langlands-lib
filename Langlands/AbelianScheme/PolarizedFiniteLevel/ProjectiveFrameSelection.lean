import Langlands.AbelianScheme.PolarizedFiniteLevel.FiniteConfiguration
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Selecting a projective frame from a configuration with sparse hyperplane sections -/

noncomputable section

universe u v w

open Module

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {I : Type w} [Fintype I]

/-- A family whose vectors other than `w` contain a basis, together with `w`
having every coordinate nonzero, spans after omitting any single basis vector. -/
theorem span_snoc_omit_eq_top {m : ℕ} (β : Module.Basis (Fin (m + 1)) K V)
    (w : V) (hw : ∀ j, β.coord j w ≠ 0) (k : Fin (m + 2)) :
    ⊤ ≤ Submodule.span K (Set.range fun j : {j : Fin (m + 2) // j ≠ k} =>
      (Fin.snoc (α := fun _ => V) (fun i => β i) w j)) := by
  classical
  set W := Submodule.span K (Set.range fun j : {j : Fin (m + 2) // j ≠ k} =>
    (Fin.snoc (α := fun _ => V) (fun i => β i) w j))
  have hmem : ∀ j : Fin (m + 2), j ≠ k → (Fin.snoc (α := fun _ => V) (fun i => β i) w j) ∈ W :=
    fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  have hβ : ∀ i : Fin (m + 1), Fin.castSucc i ≠ k → β i ∈ W := fun i hi => by
    simpa only [Fin.snoc_castSucc] using hmem _ hi
  suffices hall : ∀ i, β i ∈ W by
    rw [← β.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
  induction k using Fin.lastCases with
  | last => exact fun i => hβ i (Fin.castSucc_ne_last i)
  | cast k₀ =>
    intro i
    by_cases hi : i = k₀
    · subst hi
      have hwW : w ∈ W := by
        simpa only [Fin.snoc_last] using hmem (Fin.last _) (Fin.castSucc_ne_last i).symm
      have hsum := β.sum_repr w
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
      have hrest : ∑ j ∈ Finset.univ.erase i, β.repr w j • β j ∈ W :=
        Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
          (hβ j (fun h => Finset.ne_of_mem_erase hj (Fin.castSucc_injective _ h)))
      have hi' : β.repr w i • β i ∈ W := by
        have heq : β.repr w i • β i =
            w - ∑ j ∈ Finset.univ.erase i, β.repr w j • β j := eq_sub_iff_add_eq.mpr hsum
        rw [heq]
        exact Submodule.sub_mem _ hwW hrest
      exact (Submodule.smul_mem_iff _ (by simpa [Module.Basis.coord_apply] using hw i)).mp hi'
    · exact hβ i (fun h => hi (Fin.castSucc_injective _ h))

/-- **Frame selection.** In a space of dimension `m + 1`, a finite configuration
meeting every hyperplane in at most `q` entries, with `(m + 1) * q` smaller than its
size, contains `m + 2` entries any `m + 1` of which are linearly independent. -/
theorem HyperplaneBound.exists_frame [FiniteDimensional K V] {m : ℕ}
    (hdim : finrank K V = m + 1) {v : I → V} {q : ℕ} (h : HyperplaneBound (K := K) v q)
    (hsize : (m + 1) * q < Fintype.card I) :
    ∃ ρ : Fin (m + 2) → I, ∀ k : Fin (m + 2),
      LinearIndependent K (fun j : {j : Fin (m + 2) // j ≠ k} => v (ρ j)) := by
  classical
  have hq : q < Fintype.card I :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left q (Nat.succ_pos m)) hsize
  have hspan := h.span_eq_top hq
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K v
  rw [hspan] at hsp
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = m + 1 := by
    rw [← hdim, linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hsp,
      finrank_top]
  let e : Fin (m + 1) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let σ : Fin (m + 1) → I := a ∘ e
  have hliσ : LinearIndependent K (v ∘ σ) := hli.comp e e.injective
  have hspσ : Submodule.span K (Set.range (v ∘ σ)) = ⊤ := by
    rw [show v ∘ σ = (v ∘ a) ∘ e from rfl, Set.range_comp, e.range_eq_univ, Set.image_univ,
      hsp]
  let β : Module.Basis (Fin (m + 1)) K V := Module.Basis.mk hliσ hspσ.ge
  have hβ : ∀ i, β i = v (σ i) := fun i => Module.Basis.mk_apply hliσ hspσ.ge i
  obtain ⟨i₀, hi₀⟩ := h.exists_avoiding (fun j : Fin (m + 1) => β.coord j)
    (fun j hj => by simpa using congrArg (fun f => f (β j)) hj)
    (by simpa using hsize)
  refine ⟨Fin.snoc (α := fun _ => I) σ i₀, fun k => ?_⟩
  have key := linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_snoc_omit_eq_top β (v i₀) hi₀ k)
    (by simp [Fintype.card_subtype_compl, hdim])
  convert key using 1
  funext ⟨j, hj⟩
  induction j using Fin.lastCases with
  | last => simp
  | cast i => simp [hβ, σ]

end Langlands.AbelianScheme.PolarizedFiniteLevel
