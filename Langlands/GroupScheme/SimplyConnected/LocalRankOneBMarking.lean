import Langlands.LinearAlgebra.CartanBNumbering
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicKernelSymmetry
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.SimplyConnected.LocalRankOneCMarkedVertex

/-! # Local rank-one type-B markings and the two small-rank index alternatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

namespace TitsIndexData

/-- Type B has trivial full absolute Galois star action. -/
theorem starIsTrivial_of_type_B
    (d : TitsIndexData G) {n : ℕ} (hn : 2 ≤ n) (e : d.Vertex ≃ Fin n)
    (hB : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b)) :
    d.StarIsTrivial :=
  d.starIsTrivial_of_cartan_rigid e hB (Langlands.CartanBNumbering.rigid hn)

/-- In rank one, an actual one-vertex type-B diagram gives exactly the
published inner-A index of degree one. -/
theorem hasRankOneInnerAIndex_one_of_type_B_one
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 1)
    (hB : ∀ a b, d.cartan a b = CartanMatrix.B 1 (e a) (e b))
    (hrank : splitRank G = 1) : d.HasRankOneInnerAIndex 1 := by
  apply hasRankOneInnerAIndex_one_of_B_one e
  refine ⟨hB, ?_⟩
  intro a
  have hmarked := d.distinguishedVertices_eq_singleton_of_star_trivial hrank
    (starIsTrivial_of_equiv_fin_one e)
  rw [hmarked, Set.mem_singleton_iff]
  exact iff_true_intro (e.injective (Subsingleton.elim _ _))

end TitsIndexData

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- Under the explicit component premise, the only possible distinguished
vertex in a local rank-one B_n diagram is one of its last two vertices. -/
theorem localRankOneTypeB_marking_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) {n : ℕ} (hn : 2 ≤ n) (e : d.Vertex ≃ Fin n)
    (hB : ∀ a b, d.cartan a b = CartanMatrix.B n (e a) (e b))
    (hrank : splitRank G = 1) :
    (∃ j : Fin n, (j.val + 2 = n ∨ j.val + 1 = n) ∧
      d.IsNumberingOf (CartanMatrix.B n) (fun i => i = j) e) ∧ d.StarIsTrivial := by
  classical
  let t := d.rankOneDistinguishedVertex hrank
  let v : Fin n → d.Vertex := e.symm
  have hstar : d.StarIsTrivial := d.starIsTrivial_of_type_B hn e hB
  have hmarked := d.distinguishedVertices_eq_singleton_of_star_trivial hrank hstar
  have hz (i : Fin n) (hi : i ≠ e t.val) : v i ∈ d.zeroVertices := by
    have hn : v i ∉ d.distinguishedVertices := by
      rw [hmarked, Set.mem_singleton_iff]
      intro heq
      apply hi
      simpa only [v, Equiv.apply_symm_apply] using congrArg e heq
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not] using hn
  let last : Fin n := ⟨n - 1, by omega⟩
  let prev : Fin n := ⟨n - 2, by omega⟩
  have hj : (e t.val).val + 2 = n ∨ (e t.val).val + 1 = n := by
    by_contra h
    have hprev : prev ≠ e t.val := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [prev] at this
      omega
    have hlast : last ≠ e t.val := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [last] at this
      omega
    have hs := d.zero_cartan_symmetric_of_local_components hcomponents
      ⟨v prev, hz prev hprev⟩ ⟨v last, hz last hlast⟩
    rw [hB, hB] at hs
    simp only [v, Equiv.apply_symm_apply] at hs
    have hneq : prev ≠ last := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [prev, last] at this
      omega
    have hp : prev.val + 1 = last.val := by dsimp [prev, last]; omega
    have hr : ¬ last.val + 1 = prev.val := by dsimp [prev, last]; omega
    simp [CartanMatrix.B, hneq, hneq.symm, hp, hr, last] at hs
  refine ⟨⟨e t.val, hj, hB, ?_⟩, hstar⟩
  intro a
  change a ∈ d.distinguishedVertices ↔ e a = e t.val
  have ha : a ∈ d.distinguishedVertices ↔ a = t.val := by
    simpa only [Set.mem_singleton_iff, t] using Set.ext_iff.mp hmarked a
  exact ha.trans e.injective.eq_iff.symm

/-- The actual local rank-one B2 diagram gives the published C2 index after
interchanging the two numbered vertices. No component premise is needed. -/
theorem localRankOneTypeB_two_index
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 2)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hB : ∀ a b, d.cartan a b = CartanMatrix.B 2 (e a) (e b))
    (hrank : splitRank G = 1) :
    d.IsNumberingOf (CartanMatrix.B 2) (fun i => i.val = 0) e ∧
      d.HasRankOneCIndex 2 := by
  let q : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hq : ∀ i j : Fin 2, CartanMatrix.B 2 i j = CartanMatrix.C 2 (q i) (q j) := by
    simp only [CartanMatrix.B, CartanMatrix.C, Matrix.of_apply]
    decide
  have hC : ∀ a b, d.cartan a b = CartanMatrix.C 2 ((e.trans q) a) ((e.trans q) b) := by
    intro a b
    exact (hB a b).trans (hq (e a) (e b))
  have hmarkC := (localRankOneTypeC_presentation_and_marking
    d (e.trans q) (by decide) hsc haas hC hrank).2.1
  have hmarkB : d.IsNumberingOf (CartanMatrix.B 2) (fun i => i.val = 0) e := by
    refine ⟨hB, ?_⟩
    intro a
    have hmarked : ∀ i : Fin 2, (q i).val = 1 ↔ i.val = 0 := by decide
    exact (hmarkC.2 a).trans (hmarked (e a))
  exact ⟨hmarkB, d.hasRankOneCIndex_two_of_B_two e hmarkB⟩

end Langlands.GroupScheme
