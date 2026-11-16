import Langlands.GroupScheme.SimplyConnected.TypeE6Opposition
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicKernelCartan
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.Reductive.TitsIndexRootRestriction

/-! # The only remaining conditional local rank-one E6 marking -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The local component premise forces the distinguished E6 set to be vertex 1
and the full star action to be trivial. -/
theorem localRankOneTypeE6_marking_of_components
    (hcomponents : LocalAnisotropicCartanComponentsStatement.{u})
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hsc : IsSimplyConnected G) (hrank : splitRank G = 1) :
    d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e ∧
      d.StarIsTrivial := by
  classical
  let t := d.rankOneDistinguishedVertex hrank
  let v : Fin 6 → d.Vertex := e.symm
  let a : Fin 6 → d.pinning.rootIndex := fun i => (v i).val
  have himage (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
      (∀ b, e (d.star σ b) = e b) ∨
      (∀ b, e (d.star σ b) = Langlands.CartanE6Root.symmetry (e b)) := by
    let f : Fin 6 → Fin 6 := fun i => e (d.star σ (v i))
    have hf : ∀ i j, CartanMatrix.E 6 (f i) (f j) = CartanMatrix.E 6 i j := by
      intro i j
      calc
        CartanMatrix.E 6 (f i) (f j) = d.cartan (d.star σ (v i)) (d.star σ (v j)) :=
          (hE _ _).symm
        _ = d.cartan (v i) (v j) := d.cartan_star σ _ _
        _ = CartanMatrix.E 6 i j := by simpa [v] using hE (v i) (v j)
    rcases Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves f hf with hid | hsym
    · left
      intro b
      simpa [f, v] using hid (e b)
    · right
      intro b
      simpa [f, v] using hsym (e b)
  have hmarked (b : d.Vertex) :
      b ∈ d.distinguishedVertices ↔
        e b = e t.val ∨ e b = Langlands.CartanE6Root.symmetry (e t.val) := by
    constructor
    · intro hb
      obtain ⟨σ, hσ⟩ :=
        (d.mem_distinguishedVertices_iff_rankOne_orbit hrank b).mp hb
      rcases himage σ with hid | hsym
      · exact Or.inl ((congrArg e hσ).symm.trans (hid t.val))
      · exact Or.inr ((congrArg e hσ).symm.trans (hsym t.val))
    · rintro (hb | hb)
      · have heq : b = t.val := e.injective hb
        exact heq ▸ t.property
      · have heq : b = d.opposition t.val :=
          e.injective (hb.trans (d.opposition_eq_symmetry_of_E6 e hE hsc t.val).symm)
        rw [heq, d.opposition_mem_distinguished_iff]
        exact t.property
  have hz (i : Fin 6)
      (hi : i ≠ e t.val ∧ i ≠ Langlands.CartanE6Root.symmetry (e t.val)) :
      v i ∈ d.zeroVertices := by
    have hn : v i ∉ d.distinguishedVertices := by
      intro hd
      have hx := (hmarked (v i)).mp hd
      simp only [v, Equiv.apply_symm_apply] at hx
      exact hx.elim hi.1 hi.2
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not] using hn
  have hdist (i : Fin 6)
      (hi : i = e t.val ∨ i = Langlands.CartanE6Root.symmetry (e t.val)) :
      v i ∈ d.distinguishedVertices := by
    apply (hmarked (v i)).mpr
    simpa [v] using hi
  have hrestrict (i : Fin 6)
      (hi : i = e t.val ∨ i = Langlands.CartanE6Root.symmetry (e t.val)) :
      d.rootRestriction (a i) = d.rootRestriction t.val.val :=
    d.rootRestriction_eq_of_rank_one hrank ⟨v i, hdist i hi⟩ t
  have hpair (i j : Fin 6) :
      d.pinning.rootDatum.pairing (a i) (a j) = CartanMatrix.E 6 i j := by
    change d.cartan (v i) (v j) = _
    simpa [v] using hE (v i) (v j)
  obtain ⟨r, hr⟩ := Langlands.CartanE6Root.isRoot_highest d.pinning.rootDatum a hpair
  have hres : d.rootRestriction r =
      (∑ i : Fin 6, if i = e t.val ∨ i = Langlands.CartanE6Root.symmetry (e t.val)
        then Langlands.CartanE6Root.coefficients i else 0) • d.rootRestriction t.val.val := by
    calc
      d.rootRestriction r =
          ∑ i, Langlands.CartanE6Root.coefficients i • d.rootRestriction (a i) := by
        rw [← d.rootRestrictionHom_root, hr]
        simp only [Langlands.RootReflectionCoefficients.combination, map_sum,
          map_zsmul, d.rootRestrictionHom_root]
      _ = _ := by
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = e t.val ∨ i = Langlands.CartanE6Root.symmetry (e t.val)
        · simp only [ite_eq_left hi, hrestrict i hi]
        · rw [ite_eq_right hi, zero_smul, show d.rootRestriction (a i) = 0 from hz i
            ⟨fun h => hi (Or.inl h), fun h => hi (Or.inr h)⟩, smul_zero]
  rw [Langlands.CartanE6Root.sum_coefficients_symmetry] at hres
  have hnotbranch (ht : e t.val = 0 ∨ e t.val = 5) : False := by
    have hz1 := hz 1 (by rcases ht with ht | ht <;> simp [ht])
    have hz2 := hz 2 (by rcases ht with ht | ht <;> simp [ht])
    have hz3 := hz 3 (by rcases ht with ht | ht <;> simp [ht])
    have hz4 := hz 4 (by rcases ht with ht | ht <;> simp [ht])
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
    · exact (hnotbranch (Or.inl ht)).elim
    · rfl
    · exfalso
      apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 4) (by decide)
      simpa [ht, ofNat_zsmul] using hres
    · exfalso
      apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 3) (by decide)
      simpa [ht, ofNat_zsmul] using hres
    · exfalso
      apply d.rootRestriction_ne_nsmul_of_three_le t r (n := 4) (by decide)
      simpa [ht, ofNat_zsmul] using hres
    · exact (hnotbranch (Or.inr ht)).elim
  have hnumbering : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e := by
    refine ⟨hE, ?_⟩
    intro b
    rw [hmarked, hmark]
    simp only [Langlands.CartanE6Root.symmetry_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, or_self]
    exact Fin.ext_iff
  refine ⟨hnumbering, ?_⟩
  intro σ b
  rcases himage σ with hid | hsym
  · exact e.injective (hid b)
  · have hz3 := hz 3 (by simp [hmark])
    have hz2 := hz 2 (by simp [hmark])
    have hfix3 : d.star σ (v 3) = v 3 := by
      apply e.injective
      simpa [v] using hsym (v 3)
    have hfix2 :=
      TitsIndexData.star_eq_of_fixed_zero_adjacent_of_local_components hcomponents d σ
        ⟨v 3, hz3⟩ ⟨v 2, hz2⟩ hfix3 (by
          rw [hE]
          simp [v, CartanMatrix.E])
    have h := hsym (v 2)
    rw [hfix2] at h
    simp [v] at h

end Langlands.GroupScheme
