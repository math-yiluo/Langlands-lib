import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicKernelCartan
import Langlands.GroupScheme.SimplyConnected.LocalRankOneDStar

/-! # The local rank-one type-D bound from anisotropic Cartan components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The local anisotropic-component premise excludes rank-one type `D_n`
for every `n ≥ 6`. -/
theorem localRankOneTypeD_le_five_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 5 ≤ n)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hrank : splitRank G = 1) : n ≤ 5 := by
  have hmark := (localRankOneTypeD_presentation_and_marking_of_five_le
    d e hn hsc haas hD hrank).2.2
  by_contra h
  have hn6 : 6 ≤ n := by omega
  have hz (i : Fin n) (hi : i.val ≠ 1) : e.symm i ∈ d.zeroVertices := by
    have hnot : e.symm i ∉ d.distinguishedVertices := by
      rw [hmark]
      simpa only [Equiv.apply_symm_apply] using hi
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not] using hnot
  let c : d.zeroVertices := ⟨e.symm ⟨n - 3, by omega⟩, hz _ (by dsimp; omega)⟩
  let a : d.zeroVertices := ⟨e.symm ⟨n - 4, by omega⟩, hz _ (by dsimp; omega)⟩
  let b : d.zeroVertices := ⟨e.symm ⟨n - 2, by omega⟩, hz _ (by dsimp; omega)⟩
  let t : d.zeroVertices := ⟨e.symm ⟨n - 1, by omega⟩, hz _ (by dsimp; omega)⟩
  have hab : a ≠ b := by
    intro heq
    have hval := congrArg (fun x : d.zeroVertices => (e x.val).val) heq
    dsimp [a, b] at hval
    simp only [Equiv.apply_symm_apply] at hval
    omega
  have hat : a ≠ t := by
    intro heq
    have hval := congrArg (fun x : d.zeroVertices => (e x.val).val) heq
    dsimp [a, t] at hval
    simp only [Equiv.apply_symm_apply] at hval
    omega
  have hbt : b ≠ t := by
    intro heq
    have hval := congrArg (fun x : d.zeroVertices => (e x.val).val) heq
    dsimp [b, t] at hval
    simp only [Equiv.apply_symm_apply] at hval
    omega
  apply d.not_three_zero_neighbors_of_local_components hcomponents c a b t hab hat hbt
  all_goals
    rw [hD, Langlands.CartanDNumbering.eq_neg_one_iff (by omega)]
    dsimp [c, a, b, t]
    simp only [Equiv.apply_symm_apply]
    omega

/-- The local component premise makes the full star action of a local
rank-one type-D5 group trivial. The center of the zero A3 component is fixed
and its two adjacent zero vertices must then be fixed as well. -/
theorem localRankOneTypeD5_star_trivial_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 5)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 5 (e a) (e b))
    (hrank : splitRank G = 1) : d.StarIsTrivial := by
  have hmark := (localRankOneTypeD_presentation_and_marking_of_five_le
    d e (by decide) hsc haas hD hrank).2.2
  have hz (a : d.Vertex) (ha : (e a).val ≠ 1) : a ∈ d.zeroVertices := by
    have hnot : a ∉ d.distinguishedVertices := by rwa [hmark]
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not] using hnot
  let c : d.zeroVertices := ⟨e.symm ⟨2, by decide⟩, hz _ (by simp)⟩
  intro σ a
  by_cases ha : (e a).val + 2 < 5
  · exact d.star_fixes_nonfork_of_D (by decide) e hD σ a ha
  · have ha0 : (e a).val ≠ 1 := by omega
    have hcfix : d.star σ c.val = c.val := by
      apply d.star_fixes_nonfork_of_D (by decide) e hD
      simp [c]
    have hedge : d.cartan c.val a = -1 := by
      rw [hD, Langlands.CartanDNumbering.eq_neg_one_iff (by decide)]
      dsimp [c]
      simp only [Equiv.apply_symm_apply]
      have := (e a).isLt
      omega
    exact d.star_eq_of_fixed_zero_adjacent_of_local_components hcomponents
      σ c ⟨a, hz a ha0⟩ hcfix (by rw [hedge]; decide)

/-- The complete local rank-one type-D branch in ranks at least five,
conditional only on the explicitly stated local anisotropic-component
premise: rank five and the exact published inner-D5 index. -/
theorem localRankOneTypeD_innerD5_of_five_le_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 5 ≤ n)
    (hsc : IsSimplyConnected G) (haas : IsAbsolutelyAlmostSimple G)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hrank : splitRank G = 1) : n = 5 ∧ d.HasRankOneInnerD5Index := by
  have hn5 : n = 5 := by
    have := localRankOneTypeD_le_five_of_components hcomponents d e hn hsc haas hD hrank
    omega
  subst n
  exact ⟨rfl, d.hasRankOneInnerD5Index_of_type_D_five e hsc haas hD hrank
    (localRankOneTypeD5_star_trivial_of_components hcomponents d e hsc haas hD hrank)⟩

end Langlands.GroupScheme
