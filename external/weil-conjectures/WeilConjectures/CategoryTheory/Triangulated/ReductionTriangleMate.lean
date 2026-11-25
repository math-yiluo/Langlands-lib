/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Mates of a reduction comparison along a natural reduction triangle

Consider two "levels" of pretriangulated categories `A_Y, A_Z` (integral coefficients) and
categories `N_Y, N_Z` (reduced coefficients), with adjunctions `red ⊣ Res` between them, and
adjunctions `G ⊣ F : A_Z ⥤ A_Y` and `G' ⊣ F' : N_Z ⥤ N_Y` (typically `G = Lg^*`, `F = Rg_*`).
Let `β : G ⋙ red_Z ≅ red_Y ⋙ G'` (Pull) and `γ : F ⋙ red_Y ⟶ red_Z ⋙ F'` its mate (Push).

Suppose that the monads `T = red ⋙ Res` come with natural *reduction triangles*
`M --k--> M --η--> T M --δ--> M[1]` (`η` the unit of `red ⊣ Res`, `δ : T ⟶ [1]` natural), and
that there is an isomorphism `ι : Res_Y ⋙ G ≅ G' ⋙ Res_Z` such that

* `ι` is the mate of `β` under `red ⊣ Res` (the compatibility of (Pull) with the units), and
* `δ` commutes with `G` along `ι` and `β`.

Then `γ` is an isomorphism (`CategoryTheory.isIso_mateEquiv_of_reductionTriangle`), provided
`Res_Y` reflects isomorphisms and `F` is triangulated. Indeed `Res_Y (γ_K)`, followed by the
conjugate `F' ⋙ Res_Y ≅ Res_Z ⋙ F` of `β`, is the third component of a morphism from the
reduction triangle of `F K` to the image under `F` of the reduction triangle of `K`, whose first
two components are identities.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category Pretriangulated

/-- Two morphisms into `F.obj K` agree if their transposes under `G ⊣ F` do. -/
lemma Adjunction.eq_of_map_comp_counit {C D : Type*} [Category* C] [Category* D] {G : C ⥤ D}
    {F : D ⥤ C} (adj : G ⊣ F) {M : C} {K : D} {x y : M ⟶ F.obj K}
    (h : G.map x ≫ adj.counit.app K = G.map y ≫ adj.counit.app K) : x = y := by
  apply (adj.homEquiv _ _).symm.injective
  simpa [Adjunction.homEquiv_counit] using h

/-- A natural transformation out of `Res ⋙ G`, for an adjunction `red ⊣ Res`, is determined by its
composites with `G` of the unit. -/
lemma Adjunction.natTrans_ext_of_map_unit {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {red : C ⥤ D} {res : D ⥤ C} (adjr : red ⊣ res) {G : C ⥤ E} {H : D ⥤ E}
    {τ τ' : res ⋙ G ⟶ H}
    (h : ∀ c, G.map (adjr.unit.app c) ≫ τ.app (red.obj c) =
      G.map (adjr.unit.app c) ≫ τ'.app (red.obj c)) : τ = τ' := by
  ext N
  have e₁ := τ.naturality (adjr.counit.app N)
  have e₂ := τ'.naturality (adjr.counit.app N)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at e₁ e₂
  have e₃ : G.map (adjr.unit.app (res.obj N)) ≫ G.map (res.map (adjr.counit.app N)) = 𝟙 _ := by
    rw [← G.map_comp, adjr.right_triangle_components]
    exact G.map_id _
  calc τ.app N = (G.map (adjr.unit.app (res.obj N)) ≫ G.map (res.map (adjr.counit.app N))) ≫
        τ.app N := by rw [e₃, id_comp]
    _ = G.map (adjr.unit.app (res.obj N)) ≫ τ.app _ ≫ H.map (adjr.counit.app N) := by
        rw [assoc, e₁]
    _ = G.map (adjr.unit.app (res.obj N)) ≫ τ'.app _ ≫ H.map (adjr.counit.app N) := by
        rw [← assoc, h, assoc]
    _ = τ'.app N := by rw [← e₂, ← assoc, e₃, id_comp]

section ReductionTriangle

variable {AY AZ NY NZ : Type*} [Category* AY] [Category* AZ] [Category* NY] [Category* NZ]
  {redY : AY ⥤ NY} {resY : NY ⥤ AY} (adjY : redY ⊣ resY)
  {redZ : AZ ⥤ NZ} {resZ : NZ ⥤ AZ} (adjZ : redZ ⊣ resZ)
  {G : AY ⥤ AZ} {F : AZ ⥤ AY} (adj : G ⊣ F)
  {G' : NY ⥤ NZ} {F' : NZ ⥤ NY} (adj' : G' ⊣ F')
  (β : G ⋙ redZ ≅ redY ⋙ G') (ι : resY ⋙ G ≅ G' ⋙ resZ)

/-- If `ι` is the mate of `β` under `red ⊣ Res`, the conjugate `F' ⋙ Res_Y ≅ Res_Z ⋙ F` of `β`
is the mate of `ι` under `G ⊣ F` and `G' ⊣ F'`, in transposed form. -/
lemma map_conjugateEquiv_comp_counit (hι : mateEquiv adjY adjZ β.hom = ι.hom) (N : NZ) :
    G.map ((conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app N) ≫
        adj.counit.app (resZ.obj N) =
      ι.hom.app (F'.obj N) ≫ resZ.map (adj'.counit.app N) := by
  apply (adjZ.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, assoc]
  have h₁ := conjugateEquiv_counit (adjY.comp adj') (adj.comp adjZ) β.hom N
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_counit_app] at h₁
  rw [h₁, adjZ.counit_naturality, ← hι]
  have h₂ := mateEquiv_counit adjY adjZ β.hom (F'.obj N)
  simp only [Functor.comp_obj] at h₂
  rw [reassoc_of% h₂]

/-- `ι` is the mate of `β` under `red ⊣ Res` as soon as it is compatible with the units. -/
lemma mateEquiv_eq_of_map_unit_comp_hom_app
    (hι : ∀ M, G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M)) :
    mateEquiv adjY adjZ β.hom = ι.hom :=
  Adjunction.natTrans_ext_of_map_unit adjY fun M ↦ by
    rw [hι]
    exact unit_mateEquiv adjY adjZ β.hom M

/-- The unit form of the hypothesis that `ι` is the mate of `β`. -/
lemma map_unit_comp_hom_app (hι : mateEquiv adjY adjZ β.hom = ι.hom) (M : AY) :
    G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M) := by
  rw [← hι]
  exact unit_mateEquiv adjY adjZ β.hom M

/-- The transpose under `G ⊣ F` of `Res_Y (γ_K)` followed by the conjugate of `β`. -/
lemma map_reductionComparison_comp_counit (hι : mateEquiv adjY adjZ β.hom = ι.hom) (K : AZ) :
    G.map (resY.map ((mateEquiv adj adj' β.inv).app K) ≫
        (conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app (redZ.obj K)) ≫
        adj.counit.app (resZ.obj (redZ.obj K)) =
      ι.hom.app (redY.obj (F.obj K)) ≫ resZ.map (β.inv.app (F.obj K)) ≫
        resZ.map (redZ.map (adj.counit.app K)) := by
  rw [Functor.map_comp, assoc, map_conjugateEquiv_comp_counit adjY adjZ adj adj' β ι hι]
  have h₁ := ι.hom.naturality ((mateEquiv adj adj' β.inv).app K)
  simp only [Functor.comp_obj, Functor.comp_map] at h₁
  rw [reassoc_of% h₁, ← resZ.map_comp, ← resZ.map_comp]
  have h₂ := mateEquiv_counit adj adj' β.inv K
  simp only [Functor.comp_obj] at h₂
  rw [h₂]

/-- The comparison `Res_Y (γ_K)`, followed by the conjugate of `β`, is compatible with the units
of `red ⊣ Res`: it sends the unit at `F K` to `F` of the unit at `K`. -/
lemma unit_comp_map_reductionComparison (hι : mateEquiv adjY adjZ β.hom = ι.hom) (K : AZ) :
    adjY.unit.app (F.obj K) ≫ resY.map ((mateEquiv adj adj' β.inv).app K) ≫
        (conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app (redZ.obj K) =
      F.map (adjZ.unit.app K) := by
  refine adj.eq_of_map_comp_counit ?_
  have h := map_unit_comp_hom_app adjY adjZ β ι hι (F.obj K)
  simp only [Functor.comp_obj] at h
  have e := map_reductionComparison_comp_counit adjY adjZ adj adj' β ι hι K
  simp only [Functor.map_comp, assoc] at e ⊢
  rw [e, reassoc_of% h, ← resZ.map_comp_assoc]
  simp only [Functor.comp_obj, Iso.hom_inv_id_app, Functor.map_id, id_comp]
  have e' := adj.counit_naturality (adjZ.unit.app K)
  have e'' := adjZ.unit.naturality (adj.counit.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at e' e''
  rw [e', e'']

variable [HasShift AY ℤ] [HasShift AZ ℤ] [G.CommShift ℤ] [F.CommShift ℤ] [adj.CommShift ℤ]
  (δY : redY ⋙ resY ⟶ shiftFunctor AY (1 : ℤ)) (δZ : redZ ⋙ resZ ⟶ shiftFunctor AZ (1 : ℤ))

/-- The comparison `Res_Y (γ_K)`, followed by the conjugate of `β`, is compatible with the
connecting morphisms `δ` of the reduction triangles, if `δ` commutes with `G`. -/
lemma map_reductionComparison_comp_δ (hι : mateEquiv adjY adjZ β.hom = ι.hom)
    (hδ : ∀ M, G.map (δY.app M) ≫ (G.commShiftIso (1 : ℤ)).hom.app M =
      ι.hom.app (redY.obj M) ≫ resZ.map (β.inv.app M) ≫ δZ.app (G.obj M)) (K : AZ) :
    (resY.map ((mateEquiv adj adj' β.inv).app K) ≫
        (conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app (redZ.obj K)) ≫
        F.map (δZ.app K) ≫ (F.commShiftIso (1 : ℤ)).hom.app K =
      δY.app (F.obj K) := by
  rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).inv.app K)]
  simp only [assoc, Iso.hom_inv_id_app]
  refine adj.eq_of_map_comp_counit ?_
  have e₁ := adj.counit_naturality (δZ.app K)
  have e₂ := map_reductionComparison_comp_counit adjY adjZ adj adj' β ι hι K
  have e₃ := adj.commShiftIso_inv_app_counit_app ℤ (1 : ℤ) K
  have e₄ := δZ.naturality (adj.counit.app K)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, Functor.map_comp, assoc,
    Functor.commShiftIso_comp_inv_app, comp_id] at e₁ e₂ e₃ e₄ ⊢
  have e₃' : G.map ((F.commShiftIso (1 : ℤ)).inv.app K) ≫ adj.counit.app (K⟦(1 : ℤ)⟧) =
      (G.commShiftIso (1 : ℤ)).hom.app (F.obj K) ≫ (adj.counit.app K)⟦(1 : ℤ)⟧' := by
    rw [← e₃, Iso.hom_inv_id_app_assoc]
  rw [e₁, reassoc_of% e₂, e₃', reassoc_of% hδ, e₄]

variable [HasZeroObject AY] [Preadditive AY] [∀ n : ℤ, (shiftFunctor AY n).Additive]
  [Pretriangulated AY] [HasZeroObject AZ] [Preadditive AZ]
  [∀ n : ℤ, (shiftFunctor AZ n).Additive] [Pretriangulated AZ]

/-- **Push from Pull along natural reduction triangles**: if the monads `red ⋙ Res` carry natural
reduction triangles `M --k--> M --η--> T M --δ--> M[1]`, `ι : Res_Y ⋙ G ≅ G' ⋙ Res_Z` is the mate
of `β : G ⋙ red_Z ≅ red_Y ⋙ G'`, and `δ` commutes with `G` along `ι` and `β`, then the mate
`γ : F ⋙ red_Y ⟶ red_Z ⋙ F'` of `β⁻¹` is an isomorphism. -/
theorem isIso_mateEquiv_of_reductionTriangle [F.IsTriangulated] [resY.ReflectsIsomorphisms]
    (k : ℤ)
    (hY : ∀ M, Triangle.mk (k • 𝟙 M) (adjY.unit.app M) (δY.app M) ∈ distTriang AY)
    (hZ : ∀ M, Triangle.mk (k • 𝟙 M) (adjZ.unit.app M) (δZ.app M) ∈ distTriang AZ)
    (hι : ∀ M, G.map (adjY.unit.app M) ≫ ι.hom.app (redY.obj M) =
      adjZ.unit.app (G.obj M) ≫ resZ.map (β.hom.app M))
    (hδ : ∀ M, G.map (δY.app M) ≫ (G.commShiftIso (1 : ℤ)).hom.app M =
      ι.hom.app (redY.obj M) ≫ resZ.map (β.inv.app M) ≫ δZ.app (G.obj M)) :
    IsIso (mateEquiv adj adj' β.inv) := by
  replace hι := mateEquiv_eq_of_map_unit_comp_hom_app adjY adjZ β ι hι
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let φ : Triangle.mk (k • 𝟙 (F.obj K)) (adjY.unit.app (F.obj K)) (δY.app (F.obj K)) ⟶
      F.mapTriangle.obj (Triangle.mk (k • 𝟙 K) (adjZ.unit.app K) (δZ.app K)) :=
    { hom₁ := 𝟙 _
      hom₂ := 𝟙 _
      hom₃ := resY.map ((mateEquiv adj adj' β.inv).app K) ≫
        (conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app (redZ.obj K)
      comm₁ := by
        dsimp [Functor.mapTriangle]
        simp only [id_comp, comp_id, Functor.map_zsmul]
        erw [Functor.map_id]
      comm₂ := by
        dsimp [Functor.mapTriangle]
        rw [id_comp]
        exact unit_comp_map_reductionComparison adjY adjZ adj adj' β ι hι K
      comm₃ := by
        dsimp [Functor.mapTriangle]
        rw [Functor.map_id, comp_id]
        exact (map_reductionComparison_comp_δ adjY adjZ adj adj' β ι δY δZ hι hδ K).symm }
  have := isIso₃_of_isIso₁₂ φ (hY _) (F.map_distinguished _ (hZ K))
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)
  have : IsIso (resY.map ((mateEquiv adj adj' β.inv).app K)) :=
    IsIso.of_isIso_comp_right _
      ((conjugateEquiv (adjY.comp adj') (adj.comp adjZ) β.hom).app (redZ.obj K))
  exact isIso_of_reflects_iso _ resY

end ReductionTriangle

end CategoryTheory
