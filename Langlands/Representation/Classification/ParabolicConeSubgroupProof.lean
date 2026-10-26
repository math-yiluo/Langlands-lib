import Langlands.Representation.Classification.ParabolicConeAuxiliaryStatement
import Langlands.Representation.Geometric.StandardIntersectionsProof

/-! Matrix subgroup containments for consecutive block coarsenings. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uR

private theorem monotone_eq_of_fiber_card {m : ℕ} {α : Type*}
    [Fintype α] [LinearOrder α] (f g : Fin m → α)
    (hf : Monotone f) (hg : Monotone g)
    (hc : ∀ j, Fintype.card {i // f i = j} = Fintype.card {i // g i = j}) : f = g := by
  classical
  let e : ∀ j, {i // f i = j} ≃ {i // g i = j} := fun j => Fintype.equivOfCardEq (hc j)
  let σ : Equiv.Perm (Fin m) := Equiv.ofFiberEquiv e
  have hs : g ∘ σ = f := funext (Equiv.ofFiberEquiv_map e)
  have hm : Monotone (g ∘ σ) := hs ▸ hf
  have h := Tuple.unique_monotone (σ := σ) (τ := Equiv.refl _) hm hg
  simpa only [Equiv.coe_refl, Function.comp_id, hs] using h

private theorem card_grouped_block_coordinates {n : ℕ} (B : BlockShape n)
    {l : ℕ} (q : Fin B.length → Fin l) (j : Fin l) :
    Fintype.card {x : Fin n // q (blockIndex B x) = j} =
      ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i := by
  classical
  calc
    _ = ∑ x : Fin n, if q (blockIndex B x) = j then 1 else 0 := by
      simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ a : B.Index, if q a.1 = j then 1 else 0 := by
      simpa only [blockIndex, Equiv.symm_apply_apply] using
        (B.indexEquiv.sum_comp (fun x => if q (blockIndex B x) = j then 1 else 0)).symm
    _ = ∑ i, if q i = j then B.size i else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : q i = j <;> simp [h]
    _ = _ := by rw [Finset.sum_filter]

/-- A size-compatible monotone grouping identifies the actual coarse block of
any standard coordinate. Surjectivity is unnecessary for this identity. -/
theorem blockIndex_coarsening {n : ℕ} (B C : BlockShape n)
    (q : Fin B.length → Fin C.length) (hq : Monotone q)
    (hs : ∀ j, C.size j = ∑ i ∈ Finset.univ.filter (fun i => q i = j), B.size i)
    (x : Fin n) : blockIndex C x = q (blockIndex B x) := by
  have hcard (j : Fin C.length) :
      Fintype.card {x : Fin n // q (blockIndex B x) = j} =
        Fintype.card {x : Fin n // blockIndex C x = j} := by
    rw [card_grouped_block_coordinates B q j, ← hs j]
    have h := card_grouped_block_coordinates C id j
    simpa only [id_eq, Finset.filter_eq', Finset.mem_univ, ite_true,
      Finset.sum_singleton] using h.symm
  exact congrFun (monotone_eq_of_fiber_card _ _
    (hq.comp (blockIndex_monotone B)) (blockIndex_monotone C) hcard).symm x

/-- The Levi subgroup consists precisely of the block diagonal matrices. -/
theorem mem_leviSubgroup_iff_blockIndex {n : ℕ} (B : BlockShape n)
    (R : Type uR) [CommRing R] (g : Langlands.GeneralLinear n R) :
    g ∈ B.leviSubgroup R ↔
      ∀ a b : Fin n, blockIndex B a ≠ blockIndex B b → g a b = 0 := by
  constructor
  · rintro ⟨m, rfl⟩ a b hab
    obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
    exact B.leviEmbedding_apply_ne R m x y
      (by simpa only [blockIndex, Equiv.symm_apply_apply] using hab)
  · intro h
    have hp : g ∈ B.parabolic R := (Geometric.mem_parabolic_iff_blockIndex R B g).2
      (fun a b hab => h a b (ne_of_gt hab))
    refine ⟨B.leviProjection R ⟨g, hp⟩, ?_⟩
    apply Units.ext
    apply Matrix.ext
    intro a b
    obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
    by_cases hij : i = j
    · subst j
      exact B.leviEmbedding_apply_same R _ i x y
    · exact (B.leviEmbedding_apply_ne R _ x y hij).trans
        (h _ _ (by simpa only [blockIndex, Equiv.symm_apply_apply] using hij)).symm

/-- Every consecutive fiber-size coarsening contains the original parabolic and
Levi, over an arbitrary commutative ring. -/
theorem glBlockCoarseningSubgroups : GLBlockCoarseningSubgroupStatement.{uR} := by
  intro n B C q hq _hsurj hs R _
  constructor
  · intro g hg
    apply (Geometric.mem_parabolic_iff_blockIndex R C g).2
    intro a b hab
    rw [blockIndex_coarsening B C q hq hs a,
      blockIndex_coarsening B C q hq hs b] at hab
    exact (Geometric.mem_parabolic_iff_blockIndex R B g).1 hg a b (by
      by_contra h
      exact (not_le_of_gt hab) (hq (le_of_not_gt h)))
  · intro g hg
    apply (mem_leviSubgroup_iff_blockIndex C R g).2
    intro a b hab
    rw [blockIndex_coarsening B C q hq hs a,
      blockIndex_coarsening B C q hq hs b] at hab
    exact (mem_leviSubgroup_iff_blockIndex B R g).1 hg a b
      (fun h => hab (congrArg q h))

end Langlands
