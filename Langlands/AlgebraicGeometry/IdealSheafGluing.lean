import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Gluing ideal sheaves from affine opens -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.IdealSheafGluing

variable {X : Scheme.{u}}

/-- The ideal sheaf on `X` obtained from an ideal of `Γ(X, U)` on an affine open `U`, extended
by the largest ideal outside (the pushforward along the open immersion). -/
noncomputable def extend (U : X.affineOpens) (J : Ideal Γ(X, U.1)) : X.IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop (J.map U.1.topIso.inv.hom)).map U.1.ι

/-- The extension of `J` along an affine open with affine inclusion: its ideal on an affine
open `V` consists of the functions whose restriction to `U ∩ V` lies in the extension of `J`. -/
lemma extend_ideal (U : X.affineOpens) [IsAffineHom U.1.ι] (J : Ideal Γ(X, U.1))
    (V : X.affineOpens) :
    (extend U J).ideal V = (J.map (X.presheaf.map (homOfLE
        (show U.1.ι ''ᵁ U.1.ι ⁻¹ᵁ V.1 ≤ U.1 from Scheme.Hom.image_le_opensRange _ _ |>.trans
          (by simp))).op).hom).comap
      (X.presheaf.map (homOfLE (show U.1.ι ''ᵁ U.1.ι ⁻¹ᵁ V.1 ≤ V.1 from
        Set.image_preimage_subset _ _)).op).hom := by
  rw [extend, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, ← CommRingCat.hom_comp,
    Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map,
    ← Functor.map_comp]
  rfl

/-- **Gluing ideal sheaves from affine opens.** Let `U k` be finitely many affine opens with
affine inclusions, and `J k` ideals of `Γ(X, U k)` that agree after restriction to every affine open
inside two of them. Then some ideal sheaf has ideal `J k` over each `U k`. -/
theorem exists_ideal_eq {ι : Type*} [Finite ι] (U : ι → X.affineOpens)
    [∀ k, IsAffineHom (U k).1.ι] (J : ∀ k, Ideal Γ(X, (U k).1))
    (hJ : ∀ (i j : ι) (W : X.affineOpens) (hi : W.1 ≤ (U i).1) (hj : W.1 ≤ (U j).1),
      (J i).map (X.presheaf.map (homOfLE hi).op).hom =
        (J j).map (X.presheaf.map (homOfLE hj).op).hom) :
    ∃ I : X.IdealSheafData, ∀ k, I.ideal (U k) = J k := by
  refine ⟨⨅ k, extend (U k) (J k), fun m => ?_⟩
  rw [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  apply le_antisymm
  · refine (iInf_le _ m).trans ?_
    rw [extend_ideal]
    have hW : (U m).1.ι ''ᵁ (U m).1.ι ⁻¹ᵁ (U m).1 = (U m).1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]
    have hbij : Function.Bijective (X.presheaf.map (homOfLE
        (show (U m).1.ι ''ᵁ (U m).1.ι ⁻¹ᵁ (U m).1 ≤ (U m).1 from hW.le)).op).hom := by
      have : homOfLE (show (U m).1.ι ''ᵁ (U m).1.ι ⁻¹ᵁ (U m).1 ≤ (U m).1 from hW.le) =
          eqToHom hW := rfl
      rw [this]
      exact ConcreteCategory.bijective_of_isIso _
    rw [Ideal.comap_map_of_bijective _ hbij]
  · refine le_iInf fun k => ?_
    rw [extend_ideal]
    intro x hx
    rw [Ideal.mem_comap]
    let W : X.affineOpens := ⟨(U k).1.ι ''ᵁ (U k).1.ι ⁻¹ᵁ (U m).1,
      ((U m).2.preimage (U k).1.ι).image_of_isOpenImmersion _⟩
    have h := hJ k m W (Scheme.Hom.image_le_opensRange _ _ |>.trans (by simp))
      (Set.image_preimage_subset _ _)
    change _ ∈ (J k).map _
    rw [h]
    exact Ideal.mem_map_of_mem _ hx

/-- **Ideal sheaves agreeing on an open cover are equal.** -/
theorem eq_of_comap_eq {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) {I J : X.IdealSheafData}
    (h : ∀ i, I.comap (U i).ι = J.comap (U i).ι) : I = J := by
  have hx : ∀ x : X, ∃ (W : X.affineOpens) (i : ι), x ∈ W.1 ∧ W.1 ≤ U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).2
    exact ⟨⟨W, hW⟩, i, hxW, hWU⟩
  choose W i hxW hWU using hx
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W
    (top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) fun x => ?_
  let W' : (U (i x)).toScheme.affineOpens :=
    ⟨(U (i x)).ι ⁻¹ᵁ (W x).1, (W x).2.preimage_of_isOpenImmersion (U (i x)).ι (by
      rw [Scheme.Opens.opensRange_ι]; exact hWU x)⟩
  have himg : (U (i x)).ι ''ᵁ W'.1 = (W x).1 := by
    change (U (i x)).ι ''ᵁ ((U (i x)).ι ⁻¹ᵁ (W x).1) = (W x).1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (hWU x)
  have hI := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I (U (i x)).ι W'
  have hJ := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J (U (i x)).ι W'
  rw [h (i x), hJ] at hI
  have hinj : Function.Injective
      (Ideal.comap (((U (i x)).ι.appIso W'.1).inv.hom) : Ideal _ → Ideal _) :=
    Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((U (i x)).ι.appIso W'.1).inv).2
  have := hinj hI
  have hW : (⟨(U (i x)).ι ''ᵁ W'.1, W'.2.image_of_isOpenImmersion _⟩ : X.affineOpens) = W x :=
    Subtype.ext himg
  have key : ∀ W₀ : X.affineOpens, W₀ = W x → J.ideal W₀ = I.ideal W₀ →
      I.ideal (W x) = J.ideal (W x) := by
    rintro W₀ rfl h₀; exact h₀.symm
  exact key _ hW this

/-- **Ideal sheaves agreeing along a jointly surjective family of open immersions are equal.** -/
theorem eq_of_comap_eq' {ι : Type*} {Z : ι → Scheme.{u}} (h : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (h i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (h i))
    {I J : X.IdealSheafData} (hIJ : ∀ i, I.comap (h i) = J.comap (h i)) : I = J := by
  refine eq_of_comap_eq (fun i => (h i).opensRange) ?_ fun i => ?_
  · exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr (hcov x)
  · have e := (h i).isoOpensRange
    have key : ∀ K : X.IdealSheafData, K.comap (h i).opensRange.ι =
        (K.comap (h i)).comap (h i).isoOpensRange.inv := by
      intro K
      rw [← Scheme.IdealSheafData.comap_comp]
      congr 1
      rw [eq_comm, Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    rw [key, key, hIJ i]

end Langlands.AlgebraicGeometry.IdealSheafGluing
