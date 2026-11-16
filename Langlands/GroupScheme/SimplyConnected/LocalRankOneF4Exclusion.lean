import Langlands.LinearAlgebra.CartanF4Root
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicKernelSymmetry
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.Reductive.TitsIndexRootRestriction

/-! # Excluding local rank-one F4 from the anisotropic-component premise -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The explicit local anisotropic-component premise excludes an actual
type-F4 Tits index of split rank one. -/
theorem localRankOneTypeF4_false_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 4)
    (hF : ∀ a b, d.cartan a b = CartanMatrix.F₄ (e a) (e b))
    (hrank : splitRank G = 1) : False := by
  classical
  let t := d.rankOneDistinguishedVertex hrank
  let v : Fin 4 → d.Vertex := e.symm
  let a : Fin 4 → d.pinning.rootIndex := fun i => (v i).val
  have hstar : d.StarIsTrivial :=
    d.starIsTrivial_of_cartan_rigid e hF Langlands.CartanF4Root.rigid
  have hmarked := d.distinguishedVertices_eq_singleton_of_star_trivial hrank hstar
  have hz (i : Fin 4) (hi : i ≠ e t.val) : v i ∈ d.zeroVertices := by
    have hn : v i ∉ d.distinguishedVertices := by
      rw [hmarked, Set.mem_singleton_iff]
      intro heq
      apply hi
      simpa only [v, Equiv.apply_symm_apply] using congrArg e heq
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not] using hn
  have hpair (i j : Fin 4) :
      d.pinning.rootDatum.pairing (a i) (a j) = CartanMatrix.F₄ i j := by
    change d.cartan (v i) (v j) = _
    simpa only [v, Equiv.apply_symm_apply] using hF (v i) (v j)
  obtain ⟨r, hr⟩ := Langlands.CartanF4Root.isRoot_highest d.pinning.rootDatum a hpair
  have hres : d.rootRestriction r =
      (![2, 3, 4, 2] : Fin 4 → ℤ) (e t.val) • d.rootRestriction t.val.val := by
    calc
      d.rootRestriction r =
          ∑ j, (![2, 3, 4, 2] : Fin 4 → ℤ) j • d.rootRestriction (a j) := by
        rw [← d.rootRestrictionHom_root, hr]
        simp only [Langlands.RootReflectionCoefficients.combination, map_sum,
          map_zsmul, d.rootRestrictionHom_root]
      _ = (![2, 3, 4, 2] : Fin 4 → ℤ) (e t.val) •
          d.rootRestriction (a (e t.val)) := by
        apply Finset.sum_eq_single (e t.val)
        · intro b _ hb
          rw [show d.rootRestriction (a b) = 0 from hz b hb, smul_zero]
        · simp
      _ = _ := by simp [a, v]
  have hnotend (ht : e t.val = 0 ∨ e t.val = 3) : False := by
    have hz1 : v 1 ∈ d.zeroVertices := hz 1 (by rcases ht with h | h <;> rw [h] <;> decide)
    have hz2 : v 2 ∈ d.zeroVertices := hz 2 (by rcases ht with h | h <;> rw [h] <;> decide)
    have hs := d.zero_cartan_symmetric_of_local_components hcomponents
      ⟨v 1, hz1⟩ ⟨v 2, hz2⟩
    rw [hF, hF] at hs
    norm_num [v, CartanMatrix.F₄] at hs
  generalize ht : e t.val = j
  fin_cases j
  · exact hnotend (Or.inl ht)
  · apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 3) (by decide)
    simpa [ht, ofNat_zsmul] using hres
  · apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 4) (by decide)
    simpa [ht, ofNat_zsmul] using hres
  · exact hnotend (Or.inr ht)

end Langlands.GroupScheme
