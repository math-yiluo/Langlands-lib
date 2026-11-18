import Langlands.GroupScheme.Reductive.SpecialLinearTensorCell
import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsProof
import Langlands.GroupScheme.Torus.CharacterIsomorphism
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # The torus isogeny `𝔾ₘ × C ⟶ T` attached to a root and a coroot -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.RankOneCoverTorus

open SpecialLinearTensorCell

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The cocharacters of a split torus form a free lattice with a finite basis. -/
theorem exists_cocharacterBasis (hT : IsSplitTorus T.toGrp) :
    ∃ (I : Type u) (_ : Finite I), Nonempty (Module.Basis I ℤ (cocharacterLattice T)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  let e1 : cocharacterLattice T ≃+
      cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) :=
    { toFun := fun ν => ν ≫ eC.hom
      invFun := fun ν => ν ≫ eC.inv
      left_inv := fun ν => by simp
      right_inv := fun ν => by simp
      map_add' := fun ν ν' => Preadditive.add_comp _ _ _ _ _ _ }
  exact ⟨I, hI, ⟨(Pi.basisFun ℤ I).map
    (e1.trans (splitTorus.cocharacterLatticeEquiv k I)).toIntLinearEquiv.symm⟩⟩

/-- A character of a split torus that vanishes on every cocharacter is zero. -/
theorem character_eq_zero (hT : IsSplitTorus T.toGrp) (ψ : characterLattice T)
    (h : ∀ ν : cocharacterLattice T, ν ≫ ψ = 0) : ψ = 0 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  have h1 : eC.inv ≫ ψ = 0 := by
    apply (splitTorus.characterLatticeEquiv k I).injective
    rw [map_zero]
    funext j
    change gmEndEquiv k (splitTorus.single _ I j ≫ eC.inv ≫ ψ) = 0
    rw [← Category.assoc, h, map_zero]
  calc ψ = eC.hom ≫ eC.inv ≫ ψ := by simp
    _ = 0 := by rw [h1, Limits.comp_zero]

/-- **The torus isogeny of a rank-one root.** For a split torus `T`, a character `α` and a
cocharacter `αv` with `⟨α, αv⟩ = 2`, there are a split torus `C` and an isogeny
`t : 𝔾ₘ × C ⟶ T` that pulls `α` back to the root `χ₀ C` of `SL₂ × C` and sends the coroot
`χv₀ C` to `αv`. -/
theorem exists_torusIsogeny (hT : IsSplitTorus T.toGrp) (α : characterLattice T)
    (αv : cocharacterLattice T) (h2 : latticePairing T α αv = 2) :
    ∃ C : CommGroupScheme (Spec (CommRingCat.of k)), IsSplitTorus C.toGrp ∧
      ∃ t : CommGroupScheme.prod (Dt k) C ⟶ T, IsIsogeny (CommGroupScheme.groupHom t) ∧
        t ≫ α = χ₀ C ∧ χv₀ C ≫ t = αv := by
  classical
  obtain ⟨I, hI, ⟨bY⟩⟩ := exists_cocharacterBasis hT
  let K := LinearMap.ker (latticePairing T α)
  obtain ⟨n, bK⟩ := Submodule.basisOfPid bY K
  let J := ULift.{u} (Fin n)
  let C := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) J
  let κ : J → cocharacterLattice T := fun j => (bK j.down : cocharacterLattice T)
  have hκ : ∀ j, κ j ≫ α = 0 := by
    intro j
    have hm : latticePairing T α (κ j) = 0 := (bK j.down).2
    rw [eq_gmEndEquiv_zsmul k (κ j ≫ α), ← latticePairing_apply, hm, zero_smul]
  have hαv : αv ≫ α = (2 : ℤ) • 𝟙 _ := by
    rw [eq_gmEndEquiv_zsmul k (αv ≫ α), ← latticePairing_apply, h2]
  let t : CommGroupScheme.prod (Dt k) C ⟶ T :=
    CommGroupScheme.prodFst (Dt k) C ≫ splitTorus.proj _ _ ⟨0⟩ ≫ αv +
      CommGroupScheme.prodSnd (Dt k) C ≫ ∑ j, splitTorus.proj _ J j ≫ κ j
  have ht_char : t ≫ α = χ₀ C := by
    simp only [t, Preadditive.add_comp, Category.assoc, Preadditive.sum_comp, hκ,
      Limits.comp_zero, Finset.sum_const_zero, add_zero, hαv, Preadditive.comp_zsmul,
      Category.comp_id]
  have e1 : CommGroupScheme.prodInl (Dt k) C ≫ t = splitTorus.proj _ _ ⟨0⟩ ≫ αv := by
    simp only [t, Preadditive.comp_add, ← Category.assoc, CommGroupScheme.prodInl_fst,
      CommGroupScheme.prodInl_snd, Category.id_comp, Limits.zero_comp, add_zero]
  have e2 : CommGroupScheme.prodInr (Dt k) C ≫ t = ∑ j, splitTorus.proj _ J j ≫ κ j := by
    simp only [t, Preadditive.comp_add, ← Category.assoc, CommGroupScheme.prodInr_fst,
      CommGroupScheme.prodInr_snd, Category.id_comp, Limits.zero_comp, zero_add]
  have e3 : ∀ j, splitTorus.single _ J j ≫ (∑ j', splitTorus.proj _ J j' ≫ κ j') = κ j := by
    intro j
    rw [Preadditive.comp_sum, Finset.sum_eq_single j]
    · rw [← Category.assoc, splitTorus.single_comp_proj, ite_eq_left rfl, Category.id_comp]
    · intro j' _ hj'
      rw [← Category.assoc, splitTorus.single_comp_proj, ite_eq_right (Ne.symm hj'),
        Limits.zero_comp]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have ht_cochar : χv₀ C ≫ t = αv := by
    change (splitTorus.single _ _ ⟨0⟩ ≫ CommGroupScheme.prodInl (Dt k) C) ≫ t = αv
    rw [Category.assoc, e1, ← Category.assoc, splitTorus.single_comp_proj, ite_eq_left rfl,
      Category.id_comp]
  have hDC : IsSplitTorus (CommGroupScheme.prod (Dt k) C).toGrp :=
    IsSplitTorus.tensor (isSplitTorus_splitTorus _) (isSplitTorus_splitTorus _)
  refine ⟨C, isSplitTorus_splitTorus _, t,
    splitTorusIsogenyOfLatticeMaps k _ T t hDC hT ?_ ?_, ht_char, ht_cochar⟩
  · -- Injectivity on characters.
    intro χ χ' h
    simp only at h
    rw [← sub_eq_zero]
    have h' : t ≫ (χ - χ') = 0 := by rw [Preadditive.comp_sub, h, sub_self]
    generalize χ - χ' = ψ at h' ⊢
    apply character_eq_zero hT
    have hL : ∀ ν : cocharacterLattice T, latticePairing T ψ ν = 0 → ν ≫ ψ = 0 :=
      fun ν hν => by
        rw [eq_gmEndEquiv_zsmul k (ν ≫ ψ), ← latticePairing_apply, hν, zero_smul]
    have hαvψ : latticePairing T ψ αv = 0 := by
      rw [latticePairing_apply, ← ht_cochar, Category.assoc, h', Limits.comp_zero, map_zero]
    have hκψ : ∀ j, latticePairing T ψ (κ j) = 0 := by
      intro j
      have hj : κ j = (splitTorus.single _ J j ≫ CommGroupScheme.prodInr (Dt k) C) ≫ t := by
        rw [Category.assoc, e2, e3]
      rw [latticePairing_apply, hj, Category.assoc, h', Limits.comp_zero, map_zero]
    have hK : ∀ x ∈ K, latticePairing T ψ x = 0 := by
      intro x hx
      have hext : (latticePairing T ψ).comp K.subtype = 0 :=
        bK.ext fun i => by simpa using hκψ ⟨i⟩
      exact LinearMap.congr_fun hext ⟨x, hx⟩
    intro ν
    apply hL
    have hmem : (2 : ℤ) • ν - (latticePairing T α ν) • αv ∈ K := by
      rw [LinearMap.mem_ker, map_sub, map_zsmul, map_zsmul, h2, smul_eq_mul, smul_eq_mul]
      ring
    have h4 := hK _ hmem
    rw [map_sub, map_zsmul, map_zsmul, hαvψ, smul_zero, sub_zero, smul_eq_mul] at h4
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
  · -- Injectivity on cocharacters.
    intro μ μ' h
    simp only at h
    rw [← sub_eq_zero]
    have h' : (μ - μ') ≫ t = 0 := by rw [Preadditive.sub_comp, h, sub_self]
    generalize μ - μ' = ν at h' ⊢
    obtain ⟨a, ha_def⟩ : ∃ a : ℤ, (ν ≫ CommGroupScheme.prodFst _ _) ≫
        splitTorus.proj _ (ULift.{u} (Fin 1)) ⟨0⟩ = a • 𝟙 _ :=
      ⟨_, eq_gmEndEquiv_zsmul k _⟩
    obtain ⟨c, hc_def⟩ : ∃ c : J → ℤ, ∀ j, (ν ≫ CommGroupScheme.prodSnd _ _) ≫
        splitTorus.proj _ J j = c j • 𝟙 _ :=
      ⟨fun j => gmEndEquiv k _, fun j => eq_gmEndEquiv_zsmul k _⟩
    have hνt : ν ≫ t = a • αv + ∑ j, c j • κ j := by
      simp only [t, Preadditive.comp_add, Preadditive.comp_sum, ← Category.assoc, ha_def,
        hc_def, Preadditive.zsmul_comp, Category.id_comp]
    have hzero := hνt.symm.trans h'
    have ha0 : a = 0 := by
      have h3 := congrArg (· ≫ α) hzero
      simp only [Limits.zero_comp, Preadditive.add_comp, Preadditive.sum_comp,
        Preadditive.zsmul_comp, hαv, hκ, smul_zero, Finset.sum_const_zero, add_zero,
        smul_smul] at h3
      have h4 := congrArg (gmEndEquiv k) h3
      rw [map_zero, gmEndEquiv_zsmul_id] at h4
      omega
    have hsum : ∑ j, c j • κ j = 0 := by
      rwa [ha0, zero_smul, zero_add] at hzero
    have hc0 : ∀ j, c j = 0 := by
      have hK0 : ∑ i : Fin n, c ⟨i⟩ • bK i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero, ← hsum]
        exact Fintype.sum_equiv Equiv.ulift.symm _ _ (fun i => rfl)
      intro j
      exact Fintype.linearIndependent_iff.mp bK.linearIndependent _ hK0 j.down
    have hfst : ν ≫ CommGroupScheme.prodFst _ _ = 0 := by
      apply (splitTorus.cocharacterLatticeEquiv k (ULift.{u} (Fin 1))).injective
      rw [map_zero]
      funext i
      obtain ⟨i⟩ := i
      obtain rfl := Fin.fin_one_eq_zero i
      change gmEndEquiv k ((ν ≫ CommGroupScheme.prodFst _ _) ≫ splitTorus.proj _ _ ⟨0⟩) = 0
      rw [ha_def, ha0, zero_smul, map_zero]
    have hsnd : ν ≫ CommGroupScheme.prodSnd _ _ = 0 := by
      apply (splitTorus.cocharacterLatticeEquiv k J).injective
      rw [map_zero]
      funext j
      change gmEndEquiv k ((ν ≫ CommGroupScheme.prodSnd _ _) ≫ splitTorus.proj _ _ j) = 0
      rw [hc_def, hc0 j, zero_smul, map_zero]
    calc ν = ν ≫ 𝟙 _ := (Category.comp_id ν).symm
      _ = ν ≫ (CommGroupScheme.prodFst _ _ ≫ CommGroupScheme.prodInl _ _ +
          CommGroupScheme.prodSnd _ _ ≫ CommGroupScheme.prodInr _ _) := by
        rw [CommGroupScheme.prod_decomposition]
      _ = 0 := by
        rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hfst, hsnd,
          Limits.zero_comp, Limits.zero_comp, add_zero]

end Langlands.GroupScheme.RankOneCoverTorus
