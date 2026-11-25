/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible

/-! # Invertibility of the coordinate reindexing morphism

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-is-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

set_option backward.isDefEq.respectTransparency false in
/-- The morphism defined by the coordinate sections in a bijectively renamed order
is an isomorphism. No finiteness or nonemptiness assumption is needed.

Source: Stacks Project, Constructions, Definition 01NF and Lemma 01NE.
(blueprint: lem-weil-pbc-projective-space-reindex-is-iso).

Proof: On the open indexed by i, the free generator is the pullback of T_(b i)
under the identity. The coefficients of the other sections are T_(b j)/T_(b i).
The standardOpenIso identifies these opens with relative affine spaces over S.
After restriction over an affine open Spec R of S, the construction
homOfIsFreeGenerator therefore has the map of polynomial coordinate rings
over R sending T_j/T_i to T_(b j)/T_(b i), and fixing R by
homOfIsFreeGenerator_over. These affine opens cover the relative charts. Bijectivity of b
identifies the variables other than i with the variables other than b i, so this
ring map is an isomorphism, with inverse given by b.symm. These affine maps have
the same coordinate-ratio formulas on intersections. The maps formed by b and
b.symm compose to the identity on every standard chart, since their maps on the
base and on all coordinate ratios are identities. The standard charts cover,
so equality of these composites holds globally. Thus the displayed morphism
has a two-sided inverse. For empty coordinate types the schemes are empty and
the same chartwise equality argument applies to the empty cover. -/
theorem isIso_homOfIsFreeGenerator_reindex (β γ : Type u) (b : γ ≃ β)
    (S : Scheme.{u}) :
    let s := fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
      (twistOneSection β S (b j))
    let U := fun j : γ ↦ standardOpen β S (b j)
    let hs := fun j : γ ↦
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
    let hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (iSup_standardOpen β S)
    IsIso (homOfIsFreeGenerator s U hs (ℙ(β; S) ↘ S) hU) := by
  have normalized_homOfSections {X S : Scheme.{u}} {n : Type u}
      (g : X ⟶ S) (s : n → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)
      (i : n) (hsi : s i = 1) :
      homOfSections g s hs =
        AffineSpace.homOfVector g (fun j : {j : n // j ≠ i} ↦ s j.1) ≫
          (standardOpenIso n S i).inv ≫ (standardOpen n S i).ι := by
    let B := X.basicOpen (s i)
    have hB : B = ⊤ := by rw [show B = X.basicOpen (s i) from rfl, hsi, X.basicOpen_one]
    have hle := (homOfSections_preimage_standardOpen g s hs i).ge
    have : IsIso B.ι := by
      rw [← X.isoOfEq_hom_ι hB, ← Scheme.topIso_hom]
      infer_instance
    have hres : (homOfSections g s hs).resLE (standardOpen n S i) B hle ≫
        (standardOpenIso n S i).hom =
        B.ι ≫ AffineSpace.homOfVector g (fun j : {j : n // j ≠ i} ↦ s j.1) := by
      rw [homOfSections_resLE_standardOpenIso_hom]
      apply AffineSpace.hom_ext
      · simp [B]
      · intro j
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]
        symm
        apply X.eq_divBasicOpen
        have h1 : (X.basicOpen (s i)).ι.appTop (s i) = 1 := by
          rw [hsi, map_one]
        rw [h1, mul_one]
    apply (cancel_epi B.ι).mp
    rw [← Scheme.Hom.resLE_comp_ι _ hle]
    have hres' : (homOfSections g s hs).resLE (standardOpen n S i) B hle =
        B.ι ≫ AffineSpace.homOfVector g (fun j : {j : n // j ≠ i} ↦ s j.1) ≫
          (standardOpenIso n S i).inv := by
      apply (cancel_mono (standardOpenIso n S i).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hres
    rw [hres']
    simp only [Category.assoc]
  -- Identify chart coordinates using the normalized section family.
  have chart_coord {n : Type u} (S : Scheme.{u}) (i : n)
      (j : {j : n // j ≠ i}) :
      (standardOpenIso n S i).hom.appTop (AffineSpace.coord S j) =
        (standardOpen n S i).topIso.inv (coordRatio n S i j.1) := by
    classical
    have appLE_eq_of_eq : ∀ {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U V e),
        f.appLE U V e = g.appLE U V (h ▸ e) := by
      intro X Y f g h U V e
      cases h
      rfl
    let Y := 𝔸({j : n // j ≠ i}; S)
    let w : n → Γ(Y, ⊤) := fun a ↦ if h : a = i then 1 else AffineSpace.coord S ⟨a, h⟩
    have hwi : w i = 1 := dite_eq_left rfl
    have hwj (j : {j : n // j ≠ i}) : w j.1 = AffineSpace.coord S j := dite_eq_right j.2
    have hw : Ideal.span (Set.range w) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩)
        (by rw [hwi]; exact isUnit_one)
    have hH : homOfSections (Y ↘ S) w hw =
        (standardOpenIso n S i).inv ≫ (standardOpen n S i).ι := by
      rw [normalized_homOfSections _ w hw i hwi]
      have hh : AffineSpace.homOfVector (Y ↘ S)
          (fun j : {j : n // j ≠ i} ↦ w j.1) = 𝟙 Y := by
        apply AffineSpace.hom_ext
        · simp
        · intro j
          rw [AffineSpace.homOfVector_appTop_coord, hwj,
            Scheme.Hom.id_appTop, CommRingCat.id_apply]
      rw [hh, Category.id_comp]
    have hpre : ((standardOpenIso n S i).inv ≫ (standardOpen n S i).ι) ⁻¹ᵁ
        standardOpen n S i = ⊤ := by simp
    have hh := homOfSections_appLE_coordRatio (Y ↘ S) w hw hwi j.1 (hH.symm ▸ hpre.ge)
    rw [appLE_eq_of_eq hH, hwj] at hh
    have hh' : (standardOpenIso n S i).inv.appTop
        ((standardOpen n S i).topIso.inv (coordRatio n S i j.1)) =
        AffineSpace.coord S j := by
      have he : (standardOpen n S i).ι.appLE (standardOpen n S i) ⊤
          (standardOpen n S i).ι_preimage_self.ge = (standardOpen n S i).topIso.inv := by
        rw [Scheme.Opens.ι_appLE]
        rfl
      rw [← he, ← CommRingCat.comp_apply, Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      exact hh
    rw [← hh', ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.hom_inv_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  -- Restrict the constructed morphism and identify its affine coordinates.
  have ι_homOfIsFreeGenerator_reindex (β γ : Type u) (b : γ ≃ β)
      (S : Scheme.{u}) :
      let s : γ → Γ((Scheme.Modules.pullback (𝟙 ℙ(β; S))).obj (twist β S 1), ⊤) :=
      fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
        (twistOneSection β S (b j))
      let U := fun j : γ ↦ standardOpen β S (b j)
      let hs := fun j : γ ↦
        isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
      let hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (iSup_standardOpen β S)
      ∀ (i : γ) (k : β) (h : b i = k), (standardOpen β S k).ι ≫
        homOfIsFreeGenerator s U hs (ℙ(β; S) ↘ S) hU =
          (standardOpenIso β S k).hom ≫
            AffineSpace.reindex
              (fun j : {j : γ // j ≠ i} ↦
                (⟨b j.1, fun he ↦ j.2 (b.injective (he.trans h.symm))⟩ : {j : β // j ≠ k})) S ≫
            (standardOpenIso γ S i).inv ≫ (standardOpen γ S i).ι := by
    dsimp only
    intro i k h
    subst k
    let s : γ → Γ((Scheme.Modules.pullback (𝟙 ℙ(β; S))).obj (twist β S 1), ⊤) :=
      fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
      (twistOneSection β S (b j))
    let U := fun j : γ ↦ standardOpen β S (b j)
    let hs := fun j : γ ↦
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
    have hr (j : γ) : sectionRatio s U hs i j = coordRatio β S (b i) (b j) := by
      apply (hs i).coeff_eq_iff _ _ |>.mpr
      symm
      have ht := pullbackSection_twistOneSection_map_eq_smul (𝟙 ℙ(β; S)) (b j) (b i)
      rw [Scheme.Hom.id_app] at ht
      exact ht
    rw [ι_homOfIsFreeGenerator (s := s) (U := U) (hs := hs), localHom,
      normalized_homOfSections _ _ _ i (by simp [localSections])]
    suffices hc : AffineSpace.homOfVector ((U i).ι ≫ ℙ(β; S) ↘ S)
        (fun j : {j : γ // j ≠ i} ↦ localSections s U hs i j.1) =
        (standardOpenIso β S (b i)).hom ≫
          AffineSpace.reindex
            (fun j : {j : γ // j ≠ i} ↦
              (⟨b j.1, fun he ↦ j.2 (b.injective (he.trans rfl))⟩ :
                {j : β // j ≠ b i})) S by
      rw [hc]
      simp only [Category.assoc]
    apply AffineSpace.hom_ext
    · simp [U]
    · intro j
      rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord, chart_coord]
      simp only [localSections, hr]
      rfl
  dsimp only
  let φ := homOfIsFreeGenerator
    (fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
      (twistOneSection β S (b j)))
    (fun j : γ ↦ standardOpen β S (b j))
    (fun j : γ ↦ isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j))
    (ℙ(β; S) ↘ S) ((b.iSup_comp).trans (iSup_standardOpen β S))
  let ψ := homOfIsFreeGenerator
    (fun j : β ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(γ; S))
      (twistOneSection γ S (b.symm j)))
    (fun j : β ↦ standardOpen γ S (b.symm j))
    (fun j : β ↦
      isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(γ; S)) (b.symm j))
    (ℙ(γ; S) ↘ S) ((b.symm.iSup_comp).trans (iSup_standardOpen γ S))
  have hφ := ι_homOfIsFreeGenerator_reindex β γ b S
  have hψ := ι_homOfIsFreeGenerator_reindex γ β b.symm S
  dsimp only at hφ hψ
  change IsIso φ
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply Scheme.Opens.hom_ext_of_iSup_eq_top
      (fun i : γ ↦ standardOpen β S (b i))
      ((b.iSup_comp).trans (iSup_standardOpen β S))
    intro i
    rw [← Category.assoc, hφ i (b i) rfl]
    simp only [Category.assoc]
    rw [hψ (b i) i (b.symm_apply_apply i)]
    simp only [Iso.inv_hom_id_assoc]
    have hc :
        AffineSpace.reindex
          (fun j : {j : γ // j ≠ i} ↦
            (⟨b j.1, fun he ↦ j.2 (b.injective (he.trans rfl))⟩ :
              {j : β // j ≠ b i})) S ≫
        AffineSpace.reindex
          (fun j : {j : β // j ≠ b i} ↦
            (⟨b.symm j.1, fun he ↦
              j.2 (b.symm.injective (he.trans (b.symm_apply_apply i).symm))⟩ :
              {j : γ // j ≠ i})) S = 𝟙 _ := by
      apply AffineSpace.hom_ext
      · simp
      · intro j
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
        congr 1
        apply Subtype.ext
        exact b.apply_symm_apply j.1
    rw [reassoc_of% hc]
    simp
  · apply Scheme.Opens.hom_ext_of_iSup_eq_top
      (fun i : β ↦ standardOpen γ S (b.symm i))
      ((b.symm.iSup_comp).trans (iSup_standardOpen γ S))
    intro i
    rw [← Category.assoc, hψ i (b.symm i) rfl]
    simp only [Category.assoc]
    rw [hφ (b.symm i) i (b.apply_symm_apply i)]
    simp only [Iso.inv_hom_id_assoc]
    have hc :
        AffineSpace.reindex
          (fun j : {j : β // j ≠ i} ↦
            (⟨b.symm j.1, fun he ↦ j.2 (b.symm.injective (he.trans rfl))⟩ :
              {j : γ // j ≠ b.symm i})) S ≫
        AffineSpace.reindex
          (fun j : {j : γ // j ≠ b.symm i} ↦
            (⟨b j.1, fun he ↦
              j.2 (b.injective (he.trans (b.apply_symm_apply i).symm))⟩ :
              {j : β // j ≠ i})) S = 𝟙 _ := by
      apply AffineSpace.hom_ext
      · simp
      · intro j
        simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
          AffineSpace.reindex_appTop_coord, Scheme.Hom.id_appTop, CommRingCat.id_apply]
        congr 1
        apply Subtype.ext
        exact b.symm_apply_apply j.1
    rw [reassoc_of% hc]
    simp

end AlgebraicGeometry.ProjectiveSpace
