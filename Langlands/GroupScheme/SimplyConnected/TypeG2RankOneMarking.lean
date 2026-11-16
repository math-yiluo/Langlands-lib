import Langlands.LinearAlgebra.CartanG2Numbering
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.Reductive.TitsIndexRootRestriction

/-! # The unique possible rank-one marking in type G2 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- Type G2 has trivial full absolute Galois star action. -/
theorem starIsTrivial_of_type_G2 (e : d.Vertex ≃ Fin 2)
    (hG : ∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b)) :
    d.StarIsTrivial :=
  d.starIsTrivial_of_cartan_rigid e hG Langlands.CartanG2Numbering.rigid

/-- At split rank one, the only possible distinguished G2 vertex is the
long-root vertex, zero-based vertex zero in Mathlib's matrix. -/
theorem G2_rankOne_marking (e : d.Vertex ≃ Fin 2)
    (hG : ∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b))
    (hrank : splitRank G = 1) :
    d.IsNumberingOf CartanMatrix.G₂ (fun i => i.val = 0) e ∧ d.StarIsTrivial := by
  classical
  let t := d.rankOneDistinguishedVertex hrank
  let v : Fin 2 → d.Vertex := e.symm
  let a : Fin 2 → d.pinning.rootIndex := fun i => (v i).val
  have hstar := d.starIsTrivial_of_type_G2 e hG
  have hmarked := d.distinguishedVertices_eq_singleton_of_star_trivial hrank hstar
  have hz (i : Fin 2) (hi : i ≠ e t.val) : d.rootRestriction (a i) = 0 := by
    have hn : v i ∉ d.distinguishedVertices := by
      rw [hmarked, Set.mem_singleton_iff]
      intro heq
      apply hi
      simpa only [v, Equiv.apply_symm_apply] using congrArg e heq
    exact not_not.mp hn
  have ht : e t.val = 0 := by
    by_contra hnot
    have h1 : e t.val = 1 := by
      have hval : (e t.val).val < 2 := (e t.val).isLt
      apply Fin.ext
      have hnval : (e t.val).val ≠ 0 := by
        intro heq
        exact hnot (Fin.ext heq)
      change (e t.val).val = 1
      omega
    have hz0 : d.rootRestriction (a 0) = 0 := hz 0 (by rw [h1]; decide)
    have hres1 : d.rootRestriction (a 1) = d.rootRestriction t.val.val := by
      have heq : v 1 = t.val := by
        apply e.injective
        simpa only [v, Equiv.apply_symm_apply] using h1.symm
      exact congrArg (fun b : d.Vertex => d.rootRestriction b.val) heq
    have hpair : d.pinning.rootDatum.pairing (a 0) (a 1) = -3 := by
      change d.cartan (v 0) (v 1) = _
      rw [hG]
      simp only [v, Equiv.apply_symm_apply]
      decide
    let r := d.pinning.rootDatum.reflectionPerm (a 1) (a 0)
    have hr : d.rootRestriction r = 3 • d.rootRestriction t.val.val := by
      rw [d.rootRestriction_reflection, hpair, hz0, hres1]
      simp [ofNat_zsmul]
    exact d.rootRestriction_ne_nsmul_of_three_le t r (by decide) hr
  refine ⟨⟨hG, ?_⟩, hstar⟩
  intro b
  have hb : b ∈ d.distinguishedVertices ↔ b = t.val := by
    simpa only [Set.mem_singleton_iff, t] using Set.ext_iff.mp hmarked b
  calc
    b ∈ d.distinguishedVertices ↔ b = t.val := hb
    _ ↔ e b = e t.val := e.injective.eq_iff.symm
    _ ↔ (e b).val = 0 := by rw [ht]; exact Fin.ext_iff

end Langlands.GroupScheme.TitsIndexData
