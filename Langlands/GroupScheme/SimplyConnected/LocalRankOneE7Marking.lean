import Langlands.LinearAlgebra.CartanE7Root
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicKernelCartan
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.Reductive.TitsIndexRootRestriction

/-! # The only remaining local rank-one E7 marking from the component premise -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The local component premise forces the unique distinguished E7 vertex
to be vertex 1, and the full star action to be trivial. -/
theorem localRankOneTypeE7_marking_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b))
    (hrank : splitRank G = 1) :
    d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e ∧
      d.StarIsTrivial := by
  classical
  let t := d.rankOneDistinguishedVertex hrank
  let v : Fin 7 → d.Vertex := e.symm
  let a : Fin 7 → d.pinning.rootIndex := fun i => (v i).val
  have hstar : d.StarIsTrivial :=
    d.starIsTrivial_of_cartan_rigid e hE Langlands.CartanE7Root.rigid
  have hmarked := d.distinguishedVertices_eq_singleton_of_star_trivial hrank hstar
  have hz (i : Fin 7) (hi : i ≠ e t.val) : v i ∈ d.zeroVertices := by
    have hn : v i ∉ d.distinguishedVertices := by
      rw [hmarked, Set.mem_singleton_iff]
      intro heq
      apply hi
      simpa only [v, Equiv.apply_symm_apply] using congrArg e heq
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not] using hn
  have hpair (i j : Fin 7) :
      d.pinning.rootDatum.pairing (a i) (a j) = CartanMatrix.E 7 i j := by
    change d.cartan (v i) (v j) = _
    simpa only [v, Equiv.apply_symm_apply] using hE (v i) (v j)
  obtain ⟨r, hr⟩ := Langlands.CartanE7Root.isRoot_highest d.pinning.rootDatum a hpair
  have hres : d.rootRestriction r =
      (Langlands.CartanE7Root.coefficients : Fin 7 → ℤ) (e t.val) • d.rootRestriction t.val.val := by
    calc
      d.rootRestriction r =
          ∑ j, (Langlands.CartanE7Root.coefficients : Fin 7 → ℤ) j • d.rootRestriction (a j) := by
        rw [← d.rootRestrictionHom_root, hr]
        simp only [Langlands.RootReflectionCoefficients.combination, map_sum,
          map_zsmul, d.rootRestrictionHom_root]
      _ = (Langlands.CartanE7Root.coefficients : Fin 7 → ℤ) (e t.val) •
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
  have hmark : e t.val = 1 := by
    generalize ht : e t.val = j
    fin_cases j
    · exact (hnotbranch (by simp [ht])).elim
    · rfl
    · exfalso
      apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 3) (by decide)
      simpa [ht, Langlands.CartanE7Root.coefficients, ofNat_zsmul] using hres
    · exfalso
      apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 4) (by decide)
      simpa [ht, Langlands.CartanE7Root.coefficients, ofNat_zsmul] using hres
    · exfalso
      apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 3) (by decide)
      simpa [ht, Langlands.CartanE7Root.coefficients, ofNat_zsmul] using hres
    · exact (hnotbranch (by simp [ht])).elim
    · exact (hnotbranch (by simp [ht])).elim
  refine ⟨⟨hE, ?_⟩, hstar⟩
  intro b
  rw [hmarked, Set.mem_singleton_iff]
  constructor
  · intro hb
    rw [hb, hmark]
    rfl
  · intro hb
    apply e.injective
    rw [hmark]
    exact Fin.ext hb

end Langlands.GroupScheme
