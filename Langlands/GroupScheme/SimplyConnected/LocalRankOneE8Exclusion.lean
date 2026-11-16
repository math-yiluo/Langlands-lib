import Langlands.LinearAlgebra.CartanENumbering
import Langlands.LinearAlgebra.CartanE8Root
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicKernelCartan
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.Reductive.TitsIndexRootRestriction

/-! # Excluding local rank-one E8 from the anisotropic-component premise -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The explicit local anisotropic-component premise excludes an actual
type-E8 Tits index of split rank one. -/
theorem localRankOneTypeE8_false_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 8)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 8 (e a) (e b))
    (hrank : splitRank G = 1) : False := by
  classical
  let t := d.rankOneDistinguishedVertex hrank
  let v : Fin 8 → d.Vertex := e.symm
  let a : Fin 8 → d.pinning.rootIndex := fun i => (v i).val
  have hstar : d.StarIsTrivial :=
    d.starIsTrivial_of_cartan_rigid e hE Langlands.CartanENumbering.rigid_eight
  have hmarked := d.distinguishedVertices_eq_singleton_of_star_trivial hrank hstar
  have hz (i : Fin 8) (hi : i ≠ e t.val) : v i ∈ d.zeroVertices := by
    have hn : v i ∉ d.distinguishedVertices := by
      rw [hmarked, Set.mem_singleton_iff]
      intro heq
      apply hi
      simpa only [v, Equiv.apply_symm_apply] using congrArg e heq
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not] using hn
  have hpair (i j : Fin 8) :
      d.pinning.rootDatum.pairing (a i) (a j) = CartanMatrix.E 8 i j := by
    change d.cartan (v i) (v j) = _
    simpa only [v, Equiv.apply_symm_apply] using hE (v i) (v j)
  obtain ⟨r, hr⟩ := Langlands.CartanE8Root.isRoot_highest d.pinning.rootDatum a hpair
  have hres : d.rootRestriction r =
      (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) (e t.val) • d.rootRestriction t.val.val := by
    calc
      d.rootRestriction r =
          ∑ j, (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) j • d.rootRestriction (a j) := by
        rw [← d.rootRestrictionHom_root, hr]
        simp only [Langlands.RootReflectionCoefficients.combination, map_sum,
          map_zsmul, d.rootRestrictionHom_root]
      _ = (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ) (e t.val) •
          d.rootRestriction (a (e t.val)) := by
        apply Finset.sum_eq_single (e t.val)
        · intro b _ hb
          rw [show d.rootRestriction (a b) = 0 from hz b hb, smul_zero]
        · simp
      _ = _ := by simp [a, v]
  have hnotbranch (ht : e t.val ≠ 1 ∧ e t.val ≠ 2 ∧
      e t.val ≠ 3 ∧ e t.val ≠ 4) : False := by
    have hz1 := hz 1 ht.1.symm
    have hz2 := hz 2 ht.2.1.symm
    have hz3 := hz 3 ht.2.2.1.symm
    have hz4 := hz 4 ht.2.2.2.symm
    apply TitsIndexData.not_three_zero_neighbors_of_local_components hcomponents d
      ⟨v 3, hz3⟩ ⟨v 1, hz1⟩ ⟨v 2, hz2⟩ ⟨v 4, hz4⟩
    · intro h
      have h' := congrArg (fun x : d.zeroVertices => e x.val) h
      simp [v] at h'
    · intro h
      have h' := congrArg (fun x : d.zeroVertices => e x.val) h
      simp [v] at h'
    · intro h
      have h' := congrArg (fun x : d.zeroVertices => e x.val) h
      simp [v] at h'
    · simpa [v, CartanMatrix.E] using hE (v 3) (v 1)
    · simpa [v, CartanMatrix.E] using hE (v 3) (v 2)
    · simpa [v, CartanMatrix.E] using hE (v 3) (v 4)
  generalize ht : e t.val = j
  fin_cases j
  · exact hnotbranch (by simp [ht])
  · apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 3) (by decide)
    simpa [ht, ofNat_zsmul] using hres
  · apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 4) (by decide)
    simpa [ht, ofNat_zsmul] using hres
  · apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 6) (by decide)
    simpa [ht, ofNat_zsmul] using hres
  · apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 5) (by decide)
    simpa [ht, ofNat_zsmul] using hres
  · exact hnotbranch (by simp [ht])
  · exact hnotbranch (by simp [ht])
  · exact hnotbranch (by simp [ht])

end Langlands.GroupScheme
