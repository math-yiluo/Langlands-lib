import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.Geometric.GeometricLemmaStatement

/-! Elementary subgroup comparisons for BZ77 2.13(a),(b). -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric CategoryTheory

universe uF

section SubgroupComparisons

variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)

/-- A full upper block parabolic can have at most one block. -/
theorem block_indices_subsingleton_of_parabolic_eq_top
    (hB : B.parabolic F = ⊤) : Subsingleton (Fin B.length) := by
  classical
  refine ⟨fun i j => ?_⟩
  by_contra hij
  have hlt : ∀ i j : Fin B.length, j < i → False := by
    intro i j hji
    let a : Fin (B.size i) := ⟨0, B.positive i⟩
    let b : Fin (B.size j) := ⟨0, B.positive j⟩
    let w := Equiv.swap (B.index i a) (B.index j b)
    have hw : permutation n F w ∈ B.parabolic F := hB ▸ Subgroup.mem_top _
    have hz := (B.mem_parabolic_iff F _).mp hw i j a b hji
    have hone : permutation n F w (B.index i a) (B.index j b) = 1 := by
      simp [permutation_entry, w]
    exact one_ne_zero (hone.symm.trans hz)
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt j i h
  · exact hlt i j h

/-- If the block parabolic is full, its block diagonal Levi is full. -/
theorem leviSubgroup_eq_top_of_parabolic_eq_top
    (hB : B.parabolic F = ⊤) : B.leviSubgroup F = ⊤ := by
  let := block_indices_subsingleton_of_parabolic_eq_top B hB
  apply top_unique
  intro g hg
  let gP : B.parabolic F := ⟨g, hB ▸ Subgroup.mem_top _⟩
  refine ⟨B.leviProjection F gP, ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro a b
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
  have hij : j = i := Subsingleton.elim _ _
  subst j
  exact B.leviEmbedding_apply_same F (B.leviProjection F gP) i a b

/-- Fullness of a refined parabolic implies fullness of its refined Levi. -/
theorem refinedLevi_eq_top_of_refinedParabolic_eq_top (S : BlockRefinement B)
    (hS : refinedParabolic F B S = ⊤) : refinedLevi F B S = ⊤ := by
  classical
  apply top_unique
  intro g hg
  rw [mem_refinedLevi]
  intro i
  have hPi : (S i).parabolic F = ⊤ := by
    apply top_unique
    intro x hx
    let g' : B.Levi F := Function.update 1 i x
    have hg' : g' ∈ refinedParabolic F B S := hS ▸ Subgroup.mem_top _
    simpa [g'] using (mem_refinedParabolic F B S g').mp hg' i
  rw [leviSubgroup_eq_top_of_parabolic_eq_top (S i) hPi]
  trivial

/-- If the source intersection is the whole source Levi, conjugating that
Levi gives exactly the embedded target intersection. -/
theorem conjugatedLevi_eq_targetIntersection (w : Equiv.Perm (Fin n))
    (hS : sourceLevi F B C w = ⊤) :
    (B.leviSubgroup F).map (MulAut.conj (permutation n F w)).toMonoidHom =
      (sourceLevi F C B w⁻¹).map (C.leviEmbedding F) := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
    let m' : sourceLevi F B C w := ⟨m, hS ▸ Subgroup.mem_top _⟩
    let e := intersectionLeviConjugation F B C w
    exact ⟨(e m').val, (e m').property,
      intersectionLeviConjugation_embedding F B C w m'⟩
  · rintro ⟨m, hm, rfl⟩
    let e := intersectionLeviConjugation F B C w
    let x := e.symm ⟨m, hm⟩
    refine ⟨B.leviEmbedding F x.val, ⟨x.val, rfl⟩, ?_⟩
    have hx := intersectionLeviConjugation_embedding F B C w x
    change C.leviEmbedding F (e (e.symm ⟨m, hm⟩)).val = _ at hx
    rw [MulEquiv.apply_symm_apply] at hx
    exact hx.symm

/-- A full source refinement identifies the entire conjugated source Levi
with the embedded target refinement in the geometric lemma. -/
theorem conjugatedLevi_eq_refinement_of_source_full
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : IsIntersectionRefinement (F := F) B C w S)
    (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)
    (hfull : refinedParabolic F B S = ⊤) :
    (B.leviSubgroup F).map (MulAut.conj (permutation n F w)).toMonoidHom =
      (refinedLevi F C R).map (C.leviEmbedding F) := by
  have hs : sourceLevi F B C w = ⊤ :=
    hS.2.1.trans (refinedLevi_eq_top_of_refinedParabolic_eq_top B S hfull)
  rw [← hR.2.1]
  exact conjugatedLevi_eq_targetIntersection B C w hs

/-- If neither intersection refinement is proper, the ambient Levis are
associated by this very permutation. -/
theorem levisAssociated_of_intersection_refinements_full
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : IsIntersectionRefinement (F := F) B C w S)
    (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)
    (hfullS : refinedParabolic F B S = ⊤)
    (hfullR : refinedParabolic F C R = ⊤) :
    LevisAssociated (F := F) B C := by
  refine ⟨⟨w, ?_⟩⟩
  have h := conjugatedLevi_eq_refinement_of_source_full B C w S R hS hR hfullS
  rw [refinedLevi_eq_top_of_refinedParabolic_eq_top C R hfullR,
    Subgroup.map_top] at h
  exact h

/-- In the absence of an associated target refinement, every geometric
source refinement is proper. -/
theorem source_refinement_proper_of_no_associated_refinement
    (hBC : ¬ ∃ (R : BlockRefinement C) (w : Equiv.Perm (Fin n)),
      (B.leviSubgroup F).map (MulAut.conj (permutation n F w)).toMonoidHom =
        (refinedLevi F C R).map (C.leviEmbedding F))
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : IsIntersectionRefinement (F := F) B C w S)
    (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R) :
    refinedParabolic F B S ≠ ⊤ := by
  intro hfull
  exact hBC ⟨R, w,
    conjugatedLevi_eq_refinement_of_source_full B C w S R hS hR hfull⟩

/-- For nonassociated Levis, every surviving geometric source piece is
induced from a proper target refinement. -/
theorem target_refinement_proper_of_nonassociated_source_full
    (hBC : ¬ LevisAssociated (F := F) B C)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : IsIntersectionRefinement (F := F) B C w S)
    (hR : IsIntersectionRefinement (F := F) C B w⁻¹ R)
    (hfullS : refinedParabolic F B S = ⊤) :
    refinedParabolic F C R ≠ ⊤ := by
  intro hfullR
  exact hBC (levisAssociated_of_intersection_refinements_full B C w S R
    hS hR hfullS hfullR)

end SubgroupComparisons

end Langlands.CuspidalSupport
