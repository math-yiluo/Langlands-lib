import Langlands.GroupScheme.SimplyConnected.TypeD4StarOrbits
import Langlands.GroupScheme.Reductive.TitsIndexRootRestriction

/-! # The central distinguished vertex for a transitive type-D4 leaf action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- At split rank one the entire set of D4 leaves cannot be the
distinguished set: three equal nonzero leaf restrictions would produce
an impermissible third multiple among the actual relative roots. -/
theorem not_D4_leaves_distinguished (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hrank : splitRank G = 1) :
    ¬ (∀ a, a ∈ d.distinguishedVertices ↔ e a ≠ 1) := by
  classical
  intro hmarked
  let v : Fin 4 → d.Vertex := e.symm
  let P := d.pinning.rootDatum
  let a : Fin 4 → d.pinning.rootIndex := fun i => (v i).val
  have hpair (i j : Fin 4) : P.pairing (a i) (a j) = CartanMatrix.D 4 i j := by
    change d.cartan (v i) (v j) = _
    simpa only [v, Equiv.apply_symm_apply] using hD (v i) (v j)
  have h0 : v 0 ∈ d.distinguishedVertices := (hmarked _).mpr (by simp [v])
  have h2 : v 2 ∈ d.distinguishedVertices := (hmarked _).mpr (by simp [v])
  have h3 : v 3 ∈ d.distinguishedVertices := (hmarked _).mpr (by simp [v])
  have hc : d.rootRestriction (a 1) = 0 := by
    have hc' : v 1 ∉ d.distinguishedVertices := by
      rw [hmarked]
      simp [v]
    exact not_not.mp hc'
  have hr2 : d.rootRestriction (a 2) = d.rootRestriction (a 0) :=
    d.rootRestriction_eq_of_rank_one hrank ⟨v 2, h2⟩ ⟨v 0, h0⟩
  have hr3 : d.rootRestriction (a 3) = d.rootRestriction (a 0) :=
    d.rootRestriction_eq_of_rank_one hrank ⟨v 3, h3⟩ ⟨v 0, h0⟩
  have hp10 : P.pairing (a 1) (a 0) = -1 := by rw [hpair]; decide
  have hp12 : P.pairing (a 1) (a 2) = -1 := by rw [hpair]; decide
  have hp13 : P.pairing (a 1) (a 3) = -1 := by rw [hpair]; decide
  have hz20 : P.pairing (a 2) (a 0) = 0 := by rw [hpair]; decide
  have hz30 : P.pairing (a 3) (a 0) = 0 := by rw [hpair]; decide
  have hz32 : P.pairing (a 3) (a 2) = 0 := by rw [hpair]; decide
  let b := P.reflectionPerm (a 0) (a 1)
  let c := P.reflectionPerm (a 2) b
  let r := P.reflectionPerm (a 3) c
  have hb2 : P.pairing b (a 2) = -1 := by
    rw [← P.pairing_reflectionPerm, P.reflectionPerm_eq_of_pairing_eq_zero hz20]
    exact hp12
  have hc3 : P.pairing c (a 3) = -1 := by
    rw [← P.pairing_reflectionPerm, P.reflectionPerm_eq_of_pairing_eq_zero hz32,
      ← P.pairing_reflectionPerm, P.reflectionPerm_eq_of_pairing_eq_zero hz30]
    exact hp13
  have hb : d.rootRestriction b = d.rootRestriction (a 0) := by
    rw [d.rootRestriction_reflection, hp10, hc]
    simp
  have hc' : d.rootRestriction c = 2 • d.rootRestriction (a 0) := by
    rw [d.rootRestriction_reflection, hb2, hb, hr2]
    simp [two_smul]
  have hr : d.rootRestriction r = 3 • d.rootRestriction (a 0) := by
    rw [d.rootRestriction_reflection, hc3, hc', hr3]
    simp [succ_nsmul]
  exact d.rootRestriction_ne_nsmul_of_three_le ⟨v 0, h0⟩ r (by decide) hr

/-- A rank-one D4 index with no globally full-star-fixed leaf has
precisely the central vertex distinguished, over every field. -/
theorem D4_central_marking_of_no_fixed_leaf (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hrank : splitRank G = 1)
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a) :
    d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) e := by
  refine ⟨hD, ?_⟩
  rcases d.D4_marking_cases_of_no_fixed_leaf e hD hrank hno with hc | hl
  · simpa [Fin.ext_iff] using hc
  · exact False.elim (d.not_D4_leaves_distinguished e hD hrank hl)

end Langlands.GroupScheme.TitsIndexData
