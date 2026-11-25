/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Cohomology.CechGluing
public import WeilConjectures.AlgebraicGeometry.Cohomology.FibreVanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatOver
public import WeilConjectures.AlgebraicGeometry.Cohomology.Kunneth
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratesFibre
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Seesaw
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.Slices
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# The cross ideal of `X × Y` and the twisted module on `X × Y × Z`

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`. Let
`J` be the ideal sheaf of `{x} × Y ∪ X × {y}` in `X ×_K Y`, the external tensor product
`I_x ⊠ I_y` (`AlgebraicGeometry.TheoremOfCube.crossIdeal`). By the Künneth formula
`H¹(X × Y, J) = 0`. For an invertible module `L` on `X ×_K Y ×_K Z` we study the twist
`𝒢 = pr^* J ⊗ L` and its map to `L`: `𝒢` is flat over `Z`, its fibre cohomology in degree one
vanishes where `L` is trivial on the fibre, and over suitable affine opens the map `𝒢 ⟶ L` is
injective with image the sections vanishing on the slices `{x} × Y × Z` and `X × {y} × Z`.
Sections of `L` with prescribed restrictions to the two slices exist locally.

These are the inputs of the proof of Stacks, Tag 0BF3, in
`WeilConjectures.AlgebraicGeometry.TheoremOfCube.SpreadOut`.

## Main statements

- `AlgebraicGeometry.TheoremOfCube.subsingleton_H_one_crossIdeal`: the Künneth input
  (Stacks, Tag 0BF2).
- `AlgebraicGeometry.TheoremOfCube.hFiber_twist_eq_zero`: vanishing of the fibre cohomology.
- `AlgebraicGeometry.TheoremOfCube.injective_twistι_app`,
  `AlgebraicGeometry.TheoremOfCube.mem_range_twistι_app`: the local structure of `𝒢 ⟶ L`.
- `AlgebraicGeometry.TheoremOfCube.exists_lift`: local lifts of slice trivialisations.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped TensorProduct

namespace AlgebraicGeometry

namespace TheoremOfCube

variable {K : Type u} [Field K]

/-- On a `K`-scheme with `Γ(X, 𝒪_X) = K`, a function vanishing at a `K`-point is zero. -/
lemma eq_zero_of_mem_idealOfOpens_ker {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [Scheme.GlobalSectionsBijective K X] (x : Spec (.of K) ⟶ X) (hx : x ≫ X ↘ Spec (.of K) = 𝟙 _)
    {s : Γ(X, ⊤)} (hs : s ∈ x.ker.idealOfOpens ⊤) : s = 0 := by
  rw [Scheme.IdealSheafData.mem_idealOfOpens_iff] at hs
  have h0 : x.appTop s = 0 := by
    rw [← x.toImage_imageι]
    change x.toImage.app _ (x.imageι.app ⊤ s) = 0
    rw [hs, map_zero]
  obtain ⟨c, rfl⟩ := (Scheme.GlobalSectionsBijective.bijective_globalSectionsRingHom
    (k := K) (X := X)).2 s
  have h1 : x.appTop (Scheme.globalSectionsRingHom K c) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c := by
    change ((X ↘ Spec (.of K)).appTop ≫ x.appTop) _ = _
    rw [← Scheme.Hom.comp_appTop, hx, Scheme.Hom.id_appTop]
    rfl
  rw [h1] at h0
  have hc : c = 0 := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
    (h0.trans (map_zero _).symm)
  rw [hc, map_zero]


variable (X Y : Over (Spec (.of K)))

/-- The ideal sheaf `pr_X⁻¹ I_x ⊓ pr_Y⁻¹ I_y` of `{x} × Y ∪ X × {y}` in `X ×_K Y`. -/
noncomputable def crossIdeal (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) : (X ⊗ Y).left.IdealSheafData :=
  let : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of K)) := ⟨Y.hom⟩
  Scheme.IdealSheafData.Kunneth.prodIdeal (K := K) x.left.ker y.left.ker

/-- **The Künneth input** (Stacks, Tag 0BF2). For `X`, `Y` proper and geometrically integral
over `K` with `K`-points `x`, `y`, the first cohomology of the ideal sheaf of
`{x} × Y ∪ X × {y}` in `X ×_K Y` vanishes. -/
lemma subsingleton_H_one_crossIdeal [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) :
    Subsingleton ((crossIdeal X Y x y).toModules.H 1) := by
  let : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of K)) := ⟨Y.hom⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsSeparated (X.left ↘ Spec (.of K)) := inferInstanceAs (IsSeparated X.hom)
  have : IsSeparated (Y.left ↘ Spec (.of K)) := inferInstanceAs (IsSeparated Y.hom)
  have : Scheme.GlobalSectionsBijective K X.left :=
    have : IsProper (X.left ↘ Spec (.of K)) := inferInstanceAs (IsProper X.hom)
    have : GeometricallyIntegral (X.left ↘ Spec (.of K)) :=
      inferInstanceAs (GeometricallyIntegral X.hom)
    .of_geometricallyIntegral (k := K) (X := X.left)
  have : Scheme.GlobalSectionsBijective K Y.left :=
    have : IsProper (Y.left ↘ Spec (.of K)) := inferInstanceAs (IsProper Y.hom)
    have : GeometricallyIntegral (Y.left ↘ Spec (.of K)) :=
      inferInstanceAs (GeometricallyIntegral Y.hom)
    .of_geometricallyIntegral (k := K) (X := Y.left)
  exact Scheme.IdealSheafData.Kunneth.subsingleton_H_one_toModules_prodIdeal (K := K) _ _
    (fun s hs ↦ eq_zero_of_mem_idealOfOpens_ker x.left (Over.w x) hs)
    (fun s hs ↦ eq_zero_of_mem_idealOfOpens_ker y.left (Over.w y) hs)


variable (Z : Over (Spec (.of K)))

/-- The module `𝒢 = pr^* J ⊗ L` on `X ×_K Y ×_K Z`, for the cross ideal `J` of `X ×_K Y`. -/
noncomputable abbrev twist (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) (L : ((X ⊗ Y) ⊗ Z).left.Modules) :
    ((X ⊗ Y) ⊗ Z).left.Modules :=
  (Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).obj (crossIdeal X Y x y).toModules ⊗ L

/-- The slice `{x} × Y × Z ⟶ X × Y × Z`. -/
noncomputable abbrev sliceX (x : 𝟙_ _ ⟶ X) : (Y ⊗ Z).left ⟶ ((X ⊗ Y) ⊗ Z).left :=
  (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)).left

/-- The slice `X × {y} × Z ⟶ X × Y × Z`. -/
noncomputable abbrev sliceY (y : 𝟙_ _ ⟶ Y) : (X ⊗ Z).left ⟶ ((X ⊗ Y) ⊗ Z).left :=
  (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)).left

/-- The slice `Z ⟶ Y × Z`, `z ↦ (y, z)`. -/
noncomputable abbrev slicePt {A : Over (Spec (.of K))} (a : 𝟙_ _ ⟶ A) : Z.left ⟶ (A ⊗ Z).left :=
  (lift (toUnit Z ≫ a) (𝟙 Z)).left

/-- The two ways of including `{x} × {y} × Z` agree. -/
lemma slicePt_sliceX (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) :
    slicePt Z y ≫ sliceX X Y Z x = slicePt Z x ≫ sliceY X Y Z y := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp

/-- The identification `Z ×_{X × Y × Z} ... `: pulling back to `{x} × {y} × Z` through either
slice. -/
noncomputable abbrev sliceComparison (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) :
    (Scheme.Modules.pullback (slicePt Z y)).obj
        ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L) ≅
      (Scheme.Modules.pullback (slicePt Z x)).obj
        ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L) :=
  (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr (slicePt_sliceX X Y Z x y)).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm

private lemma coeff_eq_of_pullback_compatibility {A B C T : Scheme.{u}}
    (f : A ⟶ C) (g : B ⟶ C) (i : T ⟶ A) (j : T ⟶ B) (h : i ≫ f = j ≫ g)
    (L : C.Modules) {O : C.Opens} {ℓ : Γ(L, O)} (hℓ : Scheme.Modules.IsFreeGenerator ℓ)
    (ex : Γ((Scheme.Modules.pullback f).obj L, ⊤))
    (ey : Γ((Scheme.Modules.pullback g).obj L, ⊤))
    (hC : ((Scheme.Modules.pullbackComp i f).app L ≪≫
        (Scheme.Modules.pullbackCongr h).app L ≪≫
        ((Scheme.Modules.pullbackComp j g).app L).symm).hom.app ⊤
          (Scheme.Modules.pullbackSection i ex) = Scheme.Modules.pullbackSection j ey)
    {g₁ : Γ(A, f ⁻¹ᵁ O)} {g₂ : Γ(B, g ⁻¹ᵁ O)}
    (hg₁ : g₁ • Scheme.Modules.pullbackSection f ℓ =
      ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE le_top).op ex)
    (hg₂ : g₂ • Scheme.Modules.pullbackSection g ℓ =
      ((Scheme.Modules.pullback g).obj L).presheaf.map (homOfLE le_top).op ey) :
    i.app _ g₁ = T.presheaf.map (homOfLE (congrArg (· ⁻¹ᵁ O) h).le).op (j.app _ g₂) := by
  let e : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj L) ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback g).obj L) :=
    (Scheme.Modules.pullbackComp i f).app L ≪≫
    (Scheme.Modules.pullbackCongr h).app L ≪≫
    ((Scheme.Modules.pullbackComp j g).app L).symm
  have hW : (i ≫ f) ⁻¹ᵁ O = (j ≫ g) ⁻¹ᵁ O :=
    congrArg (· ⁻¹ᵁ O) h
  have hT := (hℓ.pullback_unit_app g).pullback_unit_app j
  have hT' := hT.map hW.le
  have h1 := congrArg (fun s ↦ e.hom.app _
    (Scheme.Modules.pullbackSection i s)) hg₁
  rw [Scheme.Modules.pullbackSection_smul, Scheme.Modules.Hom.app_smul] at h1
  erw [Scheme.Modules.pullbackComp_congr_hom_app_pullbackSection' h L ℓ]
    at h1
  rw [Scheme.Modules.pullbackSection_map, Scheme.Modules.Hom.app_presheaf_map] at h1
  erw [hC] at h1
  have h4 : j.app _ g₂ • Scheme.Modules.pullbackSection j
      (Scheme.Modules.pullbackSection g ℓ) =
      ((Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback g).obj L)).presheaf.map
        (homOfLE (j.preimage_mono le_top)).op
        (Scheme.Modules.pullbackSection j ey) := by
    rw [← Scheme.Modules.pullbackSection_smul, hg₂, Scheme.Modules.pullbackSection_map]
  have h5 : T.presheaf.map (homOfLE hW.le).op (j.app _ g₂) •
      ((Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback g).obj L)).presheaf.map (homOfLE hW.le).op
        (Scheme.Modules.pullbackSection j
          (Scheme.Modules.pullbackSection g ℓ)) =
      ((Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback g).obj L)).presheaf.map
        (homOfLE (hW.le.trans (j.preimage_mono
          (le_top : g ⁻¹ᵁ O ≤ ⊤)))).op
        (Scheme.Modules.pullbackSection j ey) := by
    rw [← Scheme.Modules.map_smul, h4]
    exact Scheme.Modules.presheaf_map_presheaf_map_apply _ _ _ _ _
  have h1' : (show Γ(T, (i ≫ f) ⁻¹ᵁ O) from
      i.app _ g₁) •
      ((Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback g).obj L)).presheaf.map (homOfLE hW.le).op
        (Scheme.Modules.pullbackSection j
          (Scheme.Modules.pullbackSection g ℓ)) =
      ((Scheme.Modules.pullback j).obj
        ((Scheme.Modules.pullback g).obj L)).presheaf.map
        (homOfLE (hW.le.trans (j.preimage_mono
          (le_top : g ⁻¹ᵁ O ≤ ⊤)))).op
        (Scheme.Modules.pullbackSection j ey) := by
    convert h1 using 2
    all_goals rfl
  exact hT'.smul_left_injective (h1'.trans h5.symm)


/-- **Compatibility of the coefficients of rigidified slice trivialisations.** Let `ex`, `ey`
be global sections of `L` on the two slices which agree on `{x} × {y} × Z`, and `ℓ` a free
generator of `L` on `O`. Then the coefficients of `ex` and `ey` with respect to `ℓ` agree on
`{x} × {y} × Z`. -/
lemma app_coeff_eq (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) (L : ((X ⊗ Y) ⊗ Z).left.Modules)
    {O : ((X ⊗ Y) ⊗ Z).left.Opens} {ℓ : Γ(L, O)} (hℓ : Scheme.Modules.IsFreeGenerator ℓ)
    (ex : Γ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L, ⊤))
    (ey : Γ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L, ⊤))
    (hC : (sliceComparison X Y Z x y L).hom.app ⊤ (Scheme.Modules.pullbackSection _ ex) =
      Scheme.Modules.pullbackSection _ ey)
    {g₁ : Γ((Y ⊗ Z).left, sliceX X Y Z x ⁻¹ᵁ O)} {g₂ : Γ((X ⊗ Z).left, sliceY X Y Z y ⁻¹ᵁ O)}
    (hg₁ : g₁ • Scheme.Modules.pullbackSection (sliceX X Y Z x) ℓ =
      ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex)
    (hg₂ : g₂ • Scheme.Modules.pullbackSection (sliceY X Y Z y) ℓ =
      ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L).presheaf.map (homOfLE le_top).op ey) :
    (slicePt Z y).app _ g₁ = Z.left.presheaf.map (homOfLE
      (congrArg (· ⁻¹ᵁ O) (slicePt_sliceX X Y Z x y)).le).op ((slicePt Z x).app _ g₂) := by
  exact coeff_eq_of_pullback_compatibility (sliceX X Y Z x) (sliceY X Y Z y)
    (slicePt Z y) (slicePt Z x) (slicePt_sliceX X Y Z x y) L hℓ ex ey hC hg₁ hg₂




set_option backward.isDefEq.respectTransparency false in
/-- **Local lifts of the slice trivialisations.** Let `ex`, `ey` be global sections of `L` on the
two slices which agree on `{x} × {y} × Z`. Over an affine open `O` on which `L` has a free
generator, there is a section of `L` restricting to `ex` and `ey` on the two slices. -/
lemma exists_lift (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) (L : ((X ⊗ Y) ⊗ Z).left.Modules)
    {O : ((X ⊗ Y) ⊗ Z).left.Opens} (hO : IsAffineOpen O) {ℓ : Γ(L, O)}
    (hℓ : Scheme.Modules.IsFreeGenerator ℓ)
    (ex : Γ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L, ⊤))
    (ey : Γ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L, ⊤))
    (hC : (sliceComparison X Y Z x y L).hom.app ⊤ (Scheme.Modules.pullbackSection _ ex) =
      Scheme.Modules.pullbackSection _ ey) :
    ∃ s : Γ(L, O), Scheme.Modules.pullbackSection (sliceX X Y Z x) s =
        ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex ∧
      Scheme.Modules.pullbackSection (sliceY X Y Z y) s =
        ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L).presheaf.map (homOfLE le_top).op ey := by
  have : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have : IsClosedImmersion y.left := isClosedImmersion_of_comp_eq_id Y.hom y.left (Over.w y)
  have hpx := isPullback_slice_left X Y Z x
  have : IsClosedImmersion (sliceX X Y Z x) := MorphismProperty.of_isPullback hpx.flip ‹_›
  have : IsClosedImmersion (sliceY X Y Z y) :=
    MorphismProperty.of_isPullback (isPullback_slice_right X Y Z y).flip ‹_›
  have hpt := isPullback_lift_toUnit_comp_left X Z x
  have : IsClosedImmersion (slicePt Z x) := MorphismProperty.of_isPullback hpt.flip ‹_›
  obtain ⟨g₁, hg₁⟩ := (hℓ.pullback_unit_app (sliceX X Y Z x)).exists_smul_eq
    (((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex)
  obtain ⟨g₂, hg₂⟩ := (hℓ.pullback_unit_app (sliceY X Y Z y)).exists_smul_eq
    (((Scheme.Modules.pullback (sliceY X Y Z y)).obj L).presheaf.map (homOfLE le_top).op ey)
  have hc := app_coeff_eq X Y Z x y L hℓ ex ey hC hg₁ hg₂
  obtain ⟨r₁, hr₁⟩ := (sliceX X Y Z x).app_surjective O hO g₁
  have hσyO : IsAffineOpen (sliceY X Y Z y ⁻¹ᵁ O) := hO.preimage _
  have hδ : g₂ - (sliceY X Y Z y).app O r₁ ∈ (slicePt Z x).ker.ideal ⟨_, hσyO⟩ := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_sub, sub_eq_zero]
    have e1 : (slicePt Z x).app _ ((sliceY X Y Z y).app O r₁) =
        (slicePt Z x ≫ sliceY X Y Z y).app O r₁ := by
      rw [Scheme.Hom.comp_app]
      rfl
    rw [e1, Scheme.Hom.congr_app (slicePt_sliceX X Y Z x y).symm O, CommRingCat.comp_apply,
      Scheme.Hom.comp_app, CommRingCat.comp_apply, hr₁]
    erw [hc]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rw [show _ ≫ _ = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  rw [hpt.ker_fst_eq_comap] at hδ
  have e : (fst X Z).left = sliceY X Y Z y ≫ (fst (X ⊗ Y) Z ≫ fst X Y).left := by
    rw [← Over.comp_left]
    congr 1
    simp
  rw [e, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.ideal_comap_appLE _ _ ⟨O, hO⟩ ⟨_, hσyO⟩ le_rfl,
    ← hpx.ker_fst_eq_comap, Scheme.Hom.ker_apply, Scheme.Hom.appLE_eq_app] at hδ
  obtain ⟨a, ha, haδ⟩ := (Ideal.mem_map_iff_of_surjective _
    ((sliceY X Y Z y).app_surjective O hO)).mp hδ
  refine ⟨(r₁ + a) • ℓ, ?_, ?_⟩
  · rw [Scheme.Modules.pullbackSection_smul, map_add, hr₁, RingHom.mem_ker.mp ha, add_zero]
    exact hg₁
  · rw [Scheme.Modules.pullbackSection_smul, map_add, haδ, add_sub_cancel]
    exact hg₂


/-- **Rigidified trivialisations on the slices.** If `L` is trivial on the two slices, there are
free generators of `L` on the slices which agree on `{x} × {y} × Z`. -/
lemma exists_isFreeGenerator_slices (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules)
    (hx : Nonempty ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L ≅ 𝟙_ _))
    (hy : Nonempty ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L ≅ 𝟙_ _)) :
    ∃ (ex : Γ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L, ⊤))
      (ey : Γ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L, ⊤)),
      Scheme.Modules.IsFreeGenerator ex ∧ Scheme.Modules.IsFreeGenerator ey ∧
      (sliceComparison X Y Z x y L).hom.app ⊤ (Scheme.Modules.pullbackSection _ ex) =
        Scheme.Modules.pullbackSection _ ey := by
  obtain ⟨αx⟩ := hx
  obtain ⟨αy⟩ := hy
  have hex := (Scheme.Modules.isFreeGenerator_one ⊤).app_hom αx.symm
  have hey := (Scheme.Modules.isFreeGenerator_one ⊤).app_hom αy.symm
  have hA := (hex.pullback_unit_app (slicePt Z y)).app_hom (sliceComparison X Y Z x y L)
  have hB := hey.pullback_unit_app (slicePt Z x)
  obtain ⟨u, hu⟩ := hB.exists_unit_smul_eq hA
  let v : Γ((X ⊗ Z).left, ⊤)ˣ := Units.map ((snd X Z).left.app ⊤).hom.toMonoidHom u
  refine ⟨_, (v : Γ((X ⊗ Z).left, ⊤)) • _, hex, hey.units_smul v, ?_⟩
  have h1 : slicePt Z x ≫ (snd X Z).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h2 : (slicePt Z x).app ⊤ ((snd X Z).left.app ⊤ u.1) = u.1 := by
    have h3 := congrArg (fun f ↦ f u.1) (Scheme.Hom.congr_app h1 ⊤)
    simp only [Scheme.Hom.comp_app, Scheme.Hom.id_app, CommRingCat.comp_apply] at h3
    exact h3.trans (by simp)
  refine hu.trans ?_
  rw [Scheme.Modules.pullbackSection_smul]
  congr 1
  exact h2.symm

variable [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom]

omit [GeometricallyIntegral X.hom] [GeometricallyIntegral Y.hom] in
lemma isFinitePresentation_crossIdeal (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) :
    SheafOfModules.IsFinitePresentation (R := (X ⊗ Y).left.ringCatSheaf)
      (crossIdeal X Y x y).toModules := by
  have : IsProper (X ⊗ Y).hom :=
    inferInstanceAs (IsProper (Limits.pullback.fst X.hom Y.hom ≫ X.hom))
  have : IsLocallyNoetherian (X ⊗ Y).left := LocallyOfFiniteType.isLocallyNoetherian (X ⊗ Y).hom
  exact Scheme.Modules.isFinitePresentation_toModules _

/-- **The fibre cohomology of `𝒢` vanishes in degree one.** If `L` is trivial on the fibre over
`t`, then `H¹((X × Y)_{κ(t)}, 𝒢_t) = H¹(X × Y, J) ⊗ κ(t) = 0`. -/
lemma hFiber_twist_eq_zero (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) [L.IsInvertible] (t : Z.left)
    (ht : Nonempty ((Scheme.Modules.pullback ((snd (X ⊗ Y) Z).left.fiberι t)).obj L ≅
      𝟙_ ((snd (X ⊗ Y) Z).left.fiber t).Modules)) :
    (twist X Y Z x y L).hFiber (snd (X ⊗ Y) Z).left 1 t = 0 := by
  have : IsProper (X ⊗ Y).hom :=
    inferInstanceAs (IsProper (Limits.pullback.fst X.hom Y.hom ≫ X.hom))
  have := isFinitePresentation_crossIdeal X Y x y
  have := Scheme.Modules.isQuasicoherent_toModules (crossIdeal X Y x y)
  set f := (snd (X ⊗ Y) Z).left
  set g := f.fiberι t
  set F := (Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).obj (crossIdeal X Y x y).toModules
  obtain ⟨e⟩ := ht
  obtain ⟨μ⟩ := Scheme.Modules.nonempty_pullback_tensorObj_iso g F L
  have h1 : (twist X Y Z x y L).hFiber f 1 t = F.hFiber f 1 t := by
    let := f.fiberOverSpecResidueField t
    exact Scheme.Modules.finrankH_congr _ (μ ≪≫ whiskerLeftIso _ e ≪≫ ρ_ _) 1
  have sq : IsPullback (fst (X ⊗ Y) Z).left f (X ⊗ Y).hom Z.hom :=
    IsPullback.of_hasPullback (X ⊗ Y).hom Z.hom
  rw [h1, Scheme.Modules.hFiber_pullback_of_isPullback (X ⊗ Y).hom _ Z.hom _ f sq,
    Scheme.Modules.hFiber_eq_finrankH]
  have := subsingleton_H_one_crossIdeal X Y x y
  exact Module.finrank_zero_of_subsingleton


omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
/-- The map `pr^* J ⟶ 𝒪` induced by the inclusion `J ⊆ 𝒪_{X × Y}`. -/
noncomputable abbrev crossι (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) :
    (Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).obj (crossIdeal X Y x y).toModules ⟶
      𝟙_ ((X ⊗ Y) ⊗ Z).left.Modules :=
  (Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).map (crossIdeal X Y x y).toModulesι ≫
    (Scheme.Modules.pullbackObjUnitIso _).hom

/-- The map `𝒢 = pr^* J ⊗ L ⟶ L` induced by the inclusion `J ⊆ 𝒪_{X × Y}`. -/
noncomputable abbrev twistι (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) (L : ((X ⊗ Y) ⊗ Z).left.Modules) :
    twist X Y Z x y L ⟶ L :=
  (crossι X Y Z x y ▷ L) ≫ (λ_ L).hom

omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
lemma twistι_app_tmulSection (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) (L : ((X ⊗ Y) ⊗ Z).left.Modules)
    {O : ((X ⊗ Y) ⊗ Z).left.Opens} (a : Γ((Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).obj
      (crossIdeal X Y x y).toModules, O)) (ℓ : Γ(L, O)) :
    (twistι X Y Z x y L).app O (Scheme.Modules.tmulSection a ℓ) =
      (Scheme.Modules.unitSectionsEquiv O).symm ((crossι X Y Z x y).app O a) • ℓ := by
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.whiskerRight_app_tmulSection, Scheme.Modules.leftUnitor_hom_app_tmulSection']


omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- Over an affine open lying over an affine open `U` of `X × Y`, the map `pr^* J ⟶ 𝒪` is
injective, by flatness of `X × Y × Z ⟶ X × Y`. -/
lemma injective_crossι_app (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) {O : ((X ⊗ Y) ⊗ Z).left.Opens}
    (hO : IsAffineOpen O) {U : (X ⊗ Y).left.Opens} (hU : IsAffineOpen U)
    (hle : O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ U) :
    Function.Injective ((crossι X Y Z x y).app O) := by
  let π := (fst (X ⊗ Y) Z).left
  let J := crossIdeal X Y x y
  have := Scheme.Modules.isQuasicoherent_toModules J
  have : Flat π := inferInstanceAs (Flat (Limits.pullback.fst (X ⊗ Y).hom Z.hom))
  let := (π.appLE U O hle).hom.toAlgebra
  obtain ⟨e, he⟩ := Scheme.Modules.exists_linearEquiv_pullback_sections π J.toModules hU hO hle
  let ιL : Γ(J.toModules, U) →ₗ[Γ((X ⊗ Y).left, U)] Γ((X ⊗ Y).left, U) :=
    { toFun := J.toModulesι.app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hflat : Module.Flat Γ((X ⊗ Y).left, U) Γ(((X ⊗ Y) ⊗ Z).left, O) :=
    π.flat_appLE hU hO hle
  let μ : Γ(((X ⊗ Y) ⊗ Z).left, O) ⊗[Γ((X ⊗ Y).left, U)] Γ(J.toModules, U) →ₗ[
      Γ(((X ⊗ Y) ⊗ Z).left, O)]
      Γ(((X ⊗ Y) ⊗ Z).left, O) :=
    (TensorProduct.AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.lTensor _ _ ιL
  have hμ : Function.Injective μ :=
    (TensorProduct.AlgebraTensorModule.rid _ _ _).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap ιL (J.injective_toModulesι_app U))
  have hcomp (w) : (Scheme.Modules.unitSectionsEquiv O).symm ((crossι X Y Z x y).app O (e w)) =
      μ w := by
    induction w using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r m =>
      have h1 : (r ⊗ₜ m : Γ(((X ⊗ Y) ⊗ Z).left, O) ⊗[Γ((X ⊗ Y).left, U)] Γ(J.toModules, U)) =
          r • (1 ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, LinearEquiv.map_smul, Scheme.Modules.Hom.app_smul, LinearEquiv.map_smul,
        LinearMap.map_smul, he]
      congr 1
      simp only [μ, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.lTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul]
      rw [Scheme.Modules.Hom.app_presheaf_map, Scheme.Modules.Hom.comp_app,
        ConcreteCategory.comp_apply, Scheme.Modules.pullback_map_app_pullbackSection,
        Algebra.smul_def, mul_one]
      erw [Scheme.Modules.pullbackObjUnitIso_hom_app_pullbackSection]
      rfl
  intro a b hab
  obtain ⟨wa, rfl⟩ := e.surjective a
  obtain ⟨wb, rfl⟩ := e.surjective b
  exact congrArg e (hμ ((hcomp wa).symm.trans ((congrArg _ hab).trans (hcomp wb))))


omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
/-- The section `pr^* m` of `pr^* J` maps to the function `pr^♯ m`. -/
lemma crossι_app_pullbackSection (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) {O : ((X ⊗ Y) ⊗ Z).left.Opens}
    {U : (X ⊗ Y).left.Opens} (hle : O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ U)
    (m : Γ((crossIdeal X Y x y).toModules, U)) :
    (Scheme.Modules.unitSectionsEquiv O).symm ((crossι X Y Z x y).app O
      (((Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).obj
        (crossIdeal X Y x y).toModules).presheaf.map (homOfLE hle).op
        (Scheme.Modules.pullbackSection _ m))) =
      (fst (X ⊗ Y) Z).left.appLE U O hle ((crossIdeal X Y x y).toModulesι.app U m) := by
  rw [Scheme.Modules.Hom.app_presheaf_map, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, Scheme.Modules.pullback_map_app_pullbackSection]
  erw [Scheme.Modules.pullbackObjUnitIso_hom_app_pullbackSection]
  rfl

omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- **Sections vanishing on both slices come from `𝒢`.** Let `O` be an affine open lying over
an affine open `U` of `X × Y`, on which `L` has a free generator `ℓ`. A section of `L` over `O`
vanishing on the slices `{x} × Y × Z` and `X × {y} × Z` lies in the image of `𝒢(O)`. -/
lemma mem_range_twistι_app (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) (L : ((X ⊗ Y) ⊗ Z).left.Modules)
    {O : ((X ⊗ Y) ⊗ Z).left.Opens} (hO : IsAffineOpen O) {U : (X ⊗ Y).left.Opens}
    (hU : IsAffineOpen U) (hle : O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ U) {ℓ : Γ(L, O)}
    (hℓ : Scheme.Modules.IsFreeGenerator ℓ) {h : Γ(L, O)}
    (hx : Scheme.Modules.pullbackSection (sliceX X Y Z x) h = 0)
    (hy : Scheme.Modules.pullbackSection (sliceY X Y Z y) h = 0) :
    h ∈ Set.range ((twistι X Y Z x y L).app O) := by
  obtain ⟨a, rfl⟩ := hℓ.exists_smul_eq h
  have : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have : IsClosedImmersion y.left := isClosedImmersion_of_comp_eq_id Y.hom y.left (Over.w y)
  have hpx := isPullback_slice_left X Y Z x
  have hpy := isPullback_slice_right X Y Z y
  have : IsClosedImmersion (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)).left :=
    MorphismProperty.of_isPullback hpx.flip ‹_›
  have : IsClosedImmersion (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)).left :=
    MorphismProperty.of_isPullback hpy.flip ‹_›
  have hker {A : Scheme.{u}} (σ : A ⟶ ((X ⊗ Y) ⊗ Z).left) [IsClosedImmersion σ]
      (hσ : Scheme.Modules.pullbackSection σ (a • ℓ) = 0) : a ∈ σ.ker.ideal ⟨O, hO⟩ := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    rw [Scheme.Modules.pullbackSection_smul] at hσ
    refine (hℓ.pullback_unit_app σ).smul_left_injective ?_
    change _ = (0 : Γ(A, σ ⁻¹ᵁ O)) • _
    rw [zero_smul]
    exact hσ
  have hax := hker _ hx
  have hay := hker _ hy
  rw [hpx.ker_fst_eq_comap, Over.comp_left, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.ideal_comap_appLE _ _ ⟨U, hU⟩ ⟨O, hO⟩ hle] at hax
  rw [hpy.ker_fst_eq_comap, Over.comp_left, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.ideal_comap_appLE _ _ ⟨U, hU⟩ ⟨O, hO⟩ hle] at hay
  let := ((fst (X ⊗ Y) Z).left.appLE U O hle).hom.toAlgebra
  have : Flat (fst (X ⊗ Y) Z).left :=
    inferInstanceAs (Flat (Limits.pullback.fst (X ⊗ Y).hom Z.hom))
  have : Module.Flat Γ((X ⊗ Y).left, U) Γ(((X ⊗ Y) ⊗ Z).left, O) :=
    (fst (X ⊗ Y) Z).left.flat_appLE hU hO hle
  have hmem : a ∈ ((crossIdeal X Y x y).ideal ⟨U, hU⟩).map
      ((fst (X ⊗ Y) Z).left.appLE U O hle).hom := by
    change a ∈ ((x.left.ker.comap (fst X Y).left).ideal ⟨U, hU⟩ ⊓
      (y.left.ker.comap (snd X Y).left).ideal ⟨U, hU⟩).map (algebraMap _ _)
    rw [Ideal.map_inf_of_flat]
    exact ⟨hax, hay⟩
  clear hax hay hx hy hker
  induction hmem using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨j, hj, rfl⟩ := hb
    obtain ⟨m, rfl⟩ : j ∈ Set.range ((crossIdeal X Y x y).toModulesι.app U) := by
      rw [Scheme.IdealSheafData.range_toModulesι_app _ ⟨U, hU⟩]
      exact hj
    refine ⟨Scheme.Modules.tmulSection (((Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).obj
      (crossIdeal X Y x y).toModules).presheaf.map (homOfLE hle).op
        (Scheme.Modules.pullbackSection _ m)) ℓ, ?_⟩
    rw [twistι_app_tmulSection, crossι_app_pullbackSection]
  | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
  | add b c _ _ hb hc =>
    obtain ⟨g₁, hg₁⟩ := hb
    obtain ⟨g₂, hg₂⟩ := hc
    exact ⟨g₁ + g₂, by rw [map_add, hg₁, hg₂, add_smul]⟩
  | smul r b _ hb =>
    obtain ⟨g, hg⟩ := hb
    exact ⟨r • g, by rw [Scheme.Modules.Hom.app_smul, hg, smul_eq_mul, mul_smul]⟩


omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
/-- Over an affine open lying over an affine open of `X × Y` on which `L` is trivial, the map
`𝒢 ⟶ L` is injective. -/
lemma injective_twistι_app (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) (L : ((X ⊗ Y) ⊗ Z).left.Modules)
    {O : ((X ⊗ Y) ⊗ Z).left.Opens} (hO : IsAffineOpen O) {U : (X ⊗ Y).left.Opens}
    (hU : IsAffineOpen U) (hle : O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ U) {ℓ : Γ(L, O)}
    (hℓ : Scheme.Modules.IsFreeGenerator ℓ) :
    Function.Injective ((twistι X Y Z x y L).app O) := by
  intro g₁ g₂ h
  obtain ⟨a₁, rfl⟩ := (hℓ.bijective_tmulSection_right le_rfl).2 g₁
  obtain ⟨a₂, rfl⟩ := (hℓ.bijective_tmulSection_right le_rfl).2 g₂
  rw [twistι_app_tmulSection, twistι_app_tmulSection] at h
  have h' := (hℓ.map le_rfl).smul_left_injective h
  rw [(Scheme.Modules.unitSectionsEquiv O).symm.injective.eq_iff] at h'
  rw [injective_crossι_app X Y Z x y hO hU hle h']


omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- The image of `pr^* J ⟶ 𝒪` over `O` lies in the ideal generated by `J`. -/
lemma crossι_app_mem_map (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) {O : ((X ⊗ Y) ⊗ Z).left.Opens}
    (hO : IsAffineOpen O) {U : (X ⊗ Y).left.Opens} (hU : IsAffineOpen U)
    (hle : O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ U)
    (a : Γ((Scheme.Modules.pullback (fst (X ⊗ Y) Z).left).obj
      (crossIdeal X Y x y).toModules, O)) :
    (Scheme.Modules.unitSectionsEquiv O).symm ((crossι X Y Z x y).app O a) ∈
      ((crossIdeal X Y x y).ideal ⟨U, hU⟩).map ((fst (X ⊗ Y) Z).left.appLE U O hle).hom := by
  have := Scheme.Modules.isQuasicoherent_toModules (crossIdeal X Y x y)
  let := ((fst (X ⊗ Y) Z).left.appLE U O hle).hom.toAlgebra
  obtain ⟨e, he⟩ := Scheme.Modules.exists_linearEquiv_pullback_sections
    (fst (X ⊗ Y) Z).left (crossIdeal X Y x y).toModules hU hO hle
  obtain ⟨w, rfl⟩ := e.surjective a
  induction w using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [map_add]
    exact Submodule.add_mem _ ha hb
  | tmul r m =>
    have h1 : (r ⊗ₜ m : Γ(((X ⊗ Y) ⊗ Z).left, O) ⊗[Γ((X ⊗ Y).left, U)]
        Γ((crossIdeal X Y x y).toModules, U)) = r • (1 ⊗ₜ m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, LinearEquiv.map_smul, Scheme.Modules.Hom.app_smul, LinearEquiv.map_smul, he,
      crossι_app_pullbackSection]
    refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
    have h := (crossIdeal X Y x y).range_toModulesι_app ⟨U, hU⟩
    exact (Set.ext_iff.mp h _).mp ⟨m, rfl⟩

omit [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
  [GeometricallyIntegral Y.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- **Sections coming from `𝒢` vanish on the slices.** -/
lemma pullbackSection_twistι_app_eq_zero (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) {O : ((X ⊗ Y) ⊗ Z).left.Opens} (hO : IsAffineOpen O)
    {U : (X ⊗ Y).left.Opens} (hU : IsAffineOpen U) (hle : O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ U)
    {ℓ : Γ(L, O)} (hℓ : Scheme.Modules.IsFreeGenerator ℓ) (c : Γ(twist X Y Z x y L, O)) :
    Scheme.Modules.pullbackSection (sliceX X Y Z x) ((twistι X Y Z x y L).app O c) = 0 ∧
      Scheme.Modules.pullbackSection (sliceY X Y Z y) ((twistι X Y Z x y L).app O c) = 0 := by
  obtain ⟨a, rfl⟩ := (hℓ.bijective_tmulSection_right le_rfl).2 c
  rw [twistι_app_tmulSection]
  have hmem := crossι_app_mem_map X Y Z x y hO hU hle a
  have hle' : crossIdeal X Y x y ≤ x.left.ker.comap (fst X Y).left := inf_le_left
  have hle'' : crossIdeal X Y x y ≤ y.left.ker.comap (snd X Y).left := inf_le_right
  have : IsClosedImmersion x.left := isClosedImmersion_of_comp_eq_id X.hom x.left (Over.w x)
  have : IsClosedImmersion y.left := isClosedImmersion_of_comp_eq_id Y.hom y.left (Over.w y)
  have hpx := isPullback_slice_left X Y Z x
  have hpy := isPullback_slice_right X Y Z y
  have : IsClosedImmersion (sliceX X Y Z x) := MorphismProperty.of_isPullback hpx.flip ‹_›
  have : IsClosedImmersion (sliceY X Y Z y) := MorphismProperty.of_isPullback hpy.flip ‹_›
  have hx : (Scheme.Modules.unitSectionsEquiv O).symm ((crossι X Y Z x y).app O a) ∈
      (sliceX X Y Z x).ker.ideal ⟨O, hO⟩ := by
    rw [hpx.ker_fst_eq_comap, Over.comp_left, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.ideal_comap_appLE _ _ ⟨U, hU⟩ ⟨O, hO⟩ hle]
    exact Ideal.map_mono (hle' ⟨U, hU⟩) hmem
  have hy : (Scheme.Modules.unitSectionsEquiv O).symm ((crossι X Y Z x y).app O a) ∈
      (sliceY X Y Z y).ker.ideal ⟨O, hO⟩ := by
    rw [hpy.ker_fst_eq_comap, Over.comp_left, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.ideal_comap_appLE _ _ ⟨U, hU⟩ ⟨O, hO⟩ hle]
    exact Ideal.map_mono (hle'' ⟨U, hU⟩) hmem
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hx hy
  rw [Scheme.Modules.pullbackSection_smul, Scheme.Modules.pullbackSection_smul, hx, hy,
    zero_smul, zero_smul]
  exact ⟨rfl, rfl⟩

end TheoremOfCube

end AlgebraicGeometry
