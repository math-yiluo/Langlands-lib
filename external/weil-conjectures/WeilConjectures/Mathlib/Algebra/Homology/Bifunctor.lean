/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Applying a functor to the complex obtained from a bifunctor

Let `F : C₁ ⥤ C₂ ⥤ D` and `F' : C₁' ⥤ C₂' ⥤ D'` be bifunctors, `G₁ : C₁ ⥤ C₁'`,
`G₂ : C₂ ⥤ C₂'` and `G : D ⥤ D'` functors, and
`τ : G (F X₁ X₂) ⟶ F' (G₁ X₁) (G₂ X₂)` a natural transformation.
If `G` is additive and preserves the coproducts defining the total complexes, we construct
the comparison morphism of complexes
`HomologicalComplex.mapBifunctorComparison τ c K₁ K₂ :
  G(mapBifunctor K₁ K₂ F c) ⟶ mapBifunctor (G₁ K₁) (G₂ K₂) F' c`,
which on the summand `G (F (K₁.X i₁) (K₂.X i₂))` is `τ` followed by the inclusion of the
summand `F' (G₁ (K₁.X i₁)) (G₂ (K₂.X i₂))`. It is natural in `K₁` and `K₂`: this is packaged
as a natural transformation of bifunctors `HomologicalComplex.mapBifunctorComparisonNatTrans`.
It is an isomorphism when `τ` is.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* C₁'] [Category* C₂'] [Category* D']
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  [HasZeroMorphisms C₁'] [HasZeroMorphisms C₂'] [Preadditive D']
  {F : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {F' : C₁' ⥤ C₂' ⥤ D'} [F'.PreservesZeroMorphisms]
  [∀ X₁, (F'.obj X₁).PreservesZeroMorphisms]
  {G₁ : C₁ ⥤ C₁'} {G₂ : C₂ ⥤ C₂'} {G : D ⥤ D'}
  [G₁.PreservesZeroMorphisms] [G₂.PreservesZeroMorphisms] [G.Additive]
  (τ : (Functor.postcompose₂.obj G).obj F ⟶ (((Functor.whiskeringLeft₂ D').obj G₁).obj G₂).obj F')
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c : ComplexShape J)
  [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c₁ c₂ c ⁻¹' {j})) G]

namespace mapBifunctor

variable {c} (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  [HasMapBifunctor K₁ K₂ F c] (j : J)

/-- If `G` preserves the coproducts defining `mapBifunctor K₁ K₂ F c`, then
`G.obj ((mapBifunctor K₁ K₂ F c).X j)` is the coproduct of the objects
`G.obj ((F.obj (K₁.X i₁)).obj (K₂.X i₂))` such that `ComplexShape.π c₁ c₂ c (i₁, i₂) = j`. -/
noncomputable def isColimitMapCofan :
    IsColimit (Cofan.mk (G.obj ((mapBifunctor K₁ K₂ F c).X j))
      (fun (x : ComplexShape.π c₁ c₂ c ⁻¹' {j}) ↦
        G.map (ιMapBifunctor K₁ K₂ F c x.1.1 x.1.2 j x.2))) :=
  isColimitCofanMkObjOfIsColimit G _ _
    (GradedObject.isColimitCofanMapObj
      ((((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).toGradedObject) _ j)

omit [Preadditive D'] in
variable {K₁ K₂ j} (G) in
/-- Extensionality for morphisms out of `G.obj ((mapBifunctor K₁ K₂ F c).X j)`, when `G`
preserves the coproduct defining `(mapBifunctor K₁ K₂ F c).X j`: it suffices to check equality
after precomposing with the images under `G` of the inclusions of the summands. -/
lemma hom_ext_of_map {A : D'} {f g : G.obj ((mapBifunctor K₁ K₂ F c).X j) ⟶ A}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j),
      G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h) ≫ f =
        G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h) ≫ g) :
    f = g :=
  Cofan.IsColimit.hom_ext (isColimitMapCofan (G := G) (F := F) K₁ K₂ j) _ _ (fun x ↦ h _ _ x.2)

end mapBifunctor

section

omit [Preadditive D] [Preadditive D'] [F.PreservesZeroMorphisms]
  [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [F'.PreservesZeroMorphisms] [∀ X₁, (F'.obj X₁).PreservesZeroMorphisms]
  [G.Additive]

variable (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)

/-- The component `G (F (K₁.X i₁) (K₂.X i₂)) ⟶ F' ((G₁ K₁).X i₁) ((G₂ K₂).X i₂)` of `τ`.
This is `(τ.app (K₁.X i₁)).app (K₂.X i₂)`; the wrapper only fixes its target in terms of the
objects `((G₁.mapHomologicalComplex c₁).obj K₁).X i₁` of the complex `G₁ K₁`, so that it can
be composed with the inclusions of the summands of `mapBifunctor (G₁ K₁) (G₂ K₂) F' c`. -/
abbrev mapBifunctorComparisonApp (i₁ : I₁) (i₂ : I₂) :
    G.obj ((F.obj (K₁.X i₁)).obj (K₂.X i₂)) ⟶
      (F'.obj (((G₁.mapHomologicalComplex c₁).obj K₁).X i₁)).obj
        (((G₂.mapHomologicalComplex c₂).obj K₂).X i₂) :=
  (τ.app (K₁.X i₁)).app (K₂.X i₂)

variable {K₁ K₂} in
/-- Naturality of `mapBifunctorComparisonApp` in the first variable:
```
G(F(K₁.X i₁, K₂.X i₂)) ──── G(F(φ, K₂.X i₂)) ───▶ G(F(L₁.X i₁', K₂.X i₂))
          │                                                │
          │ τ                                              │ τ
          ▼                                                ▼
F'(G₁(K₁.X i₁), G₂(K₂.X i₂)) ─ F'(ψ, G₂(K₂.X i₂)) ─▶ F'(G₁(L₁.X i₁'), G₂(K₂.X i₂))
```
The morphism `ψ` is `G₁.map φ` (by `hψ`), stated with the source and target of the complexes
`G₁ K₁` and `G₁ L₁`; the lemma can then be rewritten with `hψ := rfl` whatever form of
`G₁.map φ` appears in the goal (e.g. `((G₁.mapHomologicalComplex c₁).map f).f i₁`). -/
@[reassoc]
lemma mapBifunctorComparisonApp_naturality_left {L₁ : HomologicalComplex C₁ c₁} {i₁ i₁' : I₁}
    (φ : K₁.X i₁ ⟶ L₁.X i₁')
    (ψ : ((G₁.mapHomologicalComplex c₁).obj K₁).X i₁ ⟶ ((G₁.mapHomologicalComplex c₁).obj L₁).X i₁')
    (hψ : G₁.map φ = ψ) (i₂ : I₂) :
    G.map ((F.map φ).app (K₂.X i₂)) ≫ mapBifunctorComparisonApp τ L₁ K₂ i₁' i₂ =
      mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂ ≫
        (F'.map ψ).app (((G₂.mapHomologicalComplex c₂).obj K₂).X i₂) := by
  subst hψ
  exact congr_app (τ.naturality φ) (K₂.X i₂)

variable {K₁ K₂} in
/-- Naturality of `mapBifunctorComparisonApp` in the second variable:
```
G(F(K₁.X i₁, K₂.X i₂)) ──── G(F(K₁.X i₁, φ)) ───▶ G(F(K₁.X i₁, L₂.X i₂'))
          │                                                │
          │ τ                                              │ τ
          ▼                                                ▼
F'(G₁(K₁.X i₁), G₂(K₂.X i₂)) ─ F'(G₁(K₁.X i₁), ψ) ─▶ F'(G₁(K₁.X i₁), G₂(L₂.X i₂'))
```
As in `mapBifunctorComparisonApp_naturality_left`, `ψ` is `G₂.map φ` (by `hψ`). -/
@[reassoc]
lemma mapBifunctorComparisonApp_naturality_right {L₂ : HomologicalComplex C₂ c₂} {i₂ i₂' : I₂}
    (φ : K₂.X i₂ ⟶ L₂.X i₂')
    (ψ : ((G₂.mapHomologicalComplex c₂).obj K₂).X i₂ ⟶ ((G₂.mapHomologicalComplex c₂).obj L₂).X i₂')
    (hψ : G₂.map φ = ψ) (i₁ : I₁) :
    G.map ((F.obj (K₁.X i₁)).map φ) ≫ mapBifunctorComparisonApp τ K₁ L₂ i₁ i₂' =
      mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂ ≫
        (F'.obj (((G₁.mapHomologicalComplex c₁).obj K₁).X i₁)).map ψ := by
  subst hψ
  exact (τ.app (K₁.X i₁)).naturality φ

instance [h : ∀ X₁ X₂, IsIso ((τ.app X₁).app X₂)] (i₁ : I₁) (i₂ : I₂) :
    IsIso (mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂) :=
  h _ _

end

variable (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]
  [HasMapBifunctor ((G₁.mapHomologicalComplex c₁).obj K₁)
    ((G₂.mapHomologicalComplex c₂).obj K₂) F' c]
  [HasMapBifunctor ((G₁.mapHomologicalComplex c₁).obj L₁)
    ((G₂.mapHomologicalComplex c₂).obj L₂) F' c]

/-- The degree `j` component of `mapBifunctorComparison`. -/
noncomputable def mapBifunctorComparisonX (j : J) :
    G.obj ((mapBifunctor K₁ K₂ F c).X j) ⟶
      (mapBifunctor ((G₁.mapHomologicalComplex c₁).obj K₁)
        ((G₂.mapHomologicalComplex c₂).obj K₂) F' c).X j :=
  Cofan.IsColimit.desc (mapBifunctor.isColimitMapCofan (G := G) (F := F) K₁ K₂ j)
    (fun x ↦ mapBifunctorComparisonApp τ K₁ K₂ x.1.1 x.1.2 ≫
      ιMapBifunctor ((G₁.mapHomologicalComplex c₁).obj K₁)
        ((G₂.mapHomologicalComplex c₂).obj K₂) F' c x.1.1 x.1.2 j x.2)

omit [G.Additive] in
/-- The comparison `mapBifunctorComparisonX` on the summand indexed by `(i₁, i₂)`:
```
G(F(K₁.X i₁, K₂.X i₂)) ───── G(ιMapBifunctor) ─────▶ G((mapBifunctor K₁ K₂ F c).X j)
          │                                                     │
          │ τ                                                   │ mapBifunctorComparisonX
          ▼                                                     ▼
F'(G₁(K₁.X i₁), G₂(K₂.X i₂)) ─ ιMapBifunctor ─▶ (mapBifunctor (G₁ K₁) (G₂ K₂) F' c).X j
```
-/
@[reassoc (attr := simp)]
lemma map_ιMapBifunctor_mapBifunctorComparisonX (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j) :
    G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h) ≫ mapBifunctorComparisonX τ c K₁ K₂ j =
      mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂ ≫
        ιMapBifunctor ((G₁.mapHomologicalComplex c₁).obj K₁)
          ((G₂.mapHomologicalComplex c₂).obj K₂) F' c i₁ i₂ j h :=
  Cofan.IsColimit.fac (mapBifunctor.isColimitMapCofan (G := G) (F := F) K₁ K₂ j) _
    ⟨⟨i₁, i₂⟩, h⟩

@[reassoc]
lemma map_ιMapBifunctorOrZero_mapBifunctorComparisonX (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (ιMapBifunctorOrZero K₁ K₂ F c i₁ i₂ j) ≫ mapBifunctorComparisonX τ c K₁ K₂ j =
      mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂ ≫
        ιMapBifunctorOrZero ((G₁.mapHomologicalComplex c₁).obj K₁)
          ((G₂.mapHomologicalComplex c₂).obj K₂) F' c i₁ i₂ j := by
  by_cases h : ComplexShape.π c₁ c₂ c ⟨i₁, i₂⟩ = j
  · rw [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h, ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h,
      map_ιMapBifunctor_mapBifunctorComparisonX]
  · rw [ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h, ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h,
      Functor.map_zero, zero_comp, comp_zero]

@[reassoc]
lemma map_d₁_mapBifunctorComparisonX (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j) ≫ mapBifunctorComparisonX τ c K₁ K₂ j =
      mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂ ≫
        mapBifunctor.d₁ ((G₁.mapHomologicalComplex c₁).obj K₁)
          ((G₂.mapHomologicalComplex c₂).obj K₂) F' c i₁ i₂ j := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · rw [mapBifunctor.d₁_eq' _ _ _ _ h, mapBifunctor.d₁_eq' _ _ _ _ h, Units.smul_def,
      Units.smul_def, Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      Functor.map_comp, assoc, map_ιMapBifunctorOrZero_mapBifunctorComparisonX,
      mapBifunctorComparisonApp_naturality_left_assoc _ _ _ rfl]
    rfl
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h, mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h,
      Functor.map_zero, zero_comp, comp_zero]

@[reassoc]
lemma map_d₂_mapBifunctorComparisonX (i₁ : I₁) (i₂ : I₂) (j : J) :
    G.map (mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j) ≫ mapBifunctorComparisonX τ c K₁ K₂ j =
      mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂ ≫
        mapBifunctor.d₂ ((G₁.mapHomologicalComplex c₁).obj K₁)
          ((G₂.mapHomologicalComplex c₂).obj K₂) F' c i₁ i₂ j := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · rw [mapBifunctor.d₂_eq' _ _ _ _ _ h, mapBifunctor.d₂_eq' _ _ _ _ _ h, Units.smul_def,
      Units.smul_def, Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      Functor.map_comp, assoc, map_ιMapBifunctorOrZero_mapBifunctorComparisonX,
      mapBifunctorComparisonApp_naturality_right_assoc _ _ _ rfl]
    rfl
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h, mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h,
      Functor.map_zero, zero_comp, comp_zero]

-- The objects `((G.mapHomologicalComplex c).obj K).X j` and `G.obj (K.X j)` agree only up to
-- unfolding `Functor.mapHomologicalComplex`; without this option the kernel rejects the
-- elaborated term.
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison morphism `G(mapBifunctor K₁ K₂ F c) ⟶ mapBifunctor (G₁ K₁) (G₂ K₂) F' c`
induced by a natural transformation `τ : G (F X₁ X₂) ⟶ F' (G₁ X₁) (G₂ X₂)`, when `G`
preserves the coproducts defining the total complex. -/
noncomputable def mapBifunctorComparison :
    (G.mapHomologicalComplex c).obj (mapBifunctor K₁ K₂ F c) ⟶
      mapBifunctor ((G₁.mapHomologicalComplex c₁).obj K₁)
        ((G₂.mapHomologicalComplex c₂).obj K₂) F' c where
  f := mapBifunctorComparisonX τ c K₁ K₂
  comm' j j' _ := by
    refine mapBifunctor.hom_ext_of_map G (fun i₁ i₂ h ↦ ?_)
    rw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp_assoc,
      mapBifunctor.d_eq K₁ K₂, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      Functor.map_add, Preadditive.add_comp, map_d₁_mapBifunctorComparisonX,
      map_d₂_mapBifunctorComparisonX,
      map_ιMapBifunctor_mapBifunctorComparisonX_assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]

@[simp]
lemma mapBifunctorComparison_f (j : J) :
    (mapBifunctorComparison τ c K₁ K₂).f j = mapBifunctorComparisonX τ c K₁ K₂ j := rfl

-- The objects `((G.mapHomologicalComplex c).obj K).X j` and `G.obj (K.X j)` agree only up to
-- unfolding `Functor.mapHomologicalComplex`; without this option the kernel rejects the
-- elaborated term.
set_option backward.isDefEq.respectTransparency.types false in
variable {K₁ L₁ K₂ L₂} in
/-- Naturality of `mapBifunctorComparison` in both variables:
```
G(mapBifunctor K₁ K₂ F c) ──── comparison ───▶ mapBifunctor (G₁ K₁) (G₂ K₂) F' c
          │                                                  │
          │ G(mapBifunctorMap f₁ f₂)                         │ mapBifunctorMap (G₁ f₁) (G₂ f₂)
          ▼                                                  ▼
G(mapBifunctor L₁ L₂ F c) ──── comparison ───▶ mapBifunctor (G₁ L₁) (G₂ L₂) F' c
```
-/
@[reassoc]
lemma mapBifunctorComparison_naturality (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) :
    (G.mapHomologicalComplex c).map (mapBifunctorMap f₁ f₂ F c) ≫
        mapBifunctorComparison τ c L₁ L₂ =
      mapBifunctorComparison τ c K₁ K₂ ≫
        mapBifunctorMap ((G₁.mapHomologicalComplex c₁).map f₁)
          ((G₂.mapHomologicalComplex c₂).map f₂) F' c := by
  ext j
  refine mapBifunctor.hom_ext_of_map G (fun i₁ i₂ h ↦ ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    mapBifunctorComparison_f, mapBifunctorComparison_f, ← Functor.map_comp_assoc,
    ι_mapBifunctorMap, map_ιMapBifunctor_mapBifunctorComparisonX_assoc,
    ι_mapBifunctorMap, Functor.map_comp, Functor.map_comp, assoc, assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX,
    mapBifunctorComparisonApp_naturality_right_assoc _ _ _ rfl,
    mapBifunctorComparisonApp_naturality_left_assoc _ _ _ rfl]
  rfl

instance [∀ X₁ X₂, IsIso ((τ.app X₁).app X₂)] (j : J) :
    IsIso (mapBifunctorComparisonX τ c K₁ K₂ j) := by
  refine ⟨mapBifunctorDesc (fun i₁ i₂ h ↦ inv (mapBifunctorComparisonApp τ K₁ K₂ i₁ i₂) ≫
    G.map (ιMapBifunctor K₁ K₂ F c i₁ i₂ j h)), ?_, ?_⟩
  · refine mapBifunctor.hom_ext_of_map G (fun i₁ i₂ h ↦ ?_)
    rw [map_ιMapBifunctor_mapBifunctorComparisonX_assoc, ι_mapBifunctorDesc,
      IsIso.hom_inv_id_assoc, comp_id]
  · ext i₁ i₂ h
    rw [ι_mapBifunctorDesc_assoc, assoc, map_ιMapBifunctor_mapBifunctorComparisonX,
      IsIso.inv_hom_id_assoc, comp_id]

instance [∀ X₁ X₂, IsIso ((τ.app X₁).app X₂)] :
    IsIso (mapBifunctorComparison τ c K₁ K₂) := by
  have (j : J) : IsIso ((mapBifunctorComparison τ c K₁ K₂).f j) :=
    inferInstanceAs (IsIso (mapBifunctorComparisonX τ c K₁ K₂ j))
  apply Hom.isIso_of_components

section

variable [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
    HasMapBifunctor K₁ K₂ F c]
  [∀ (K₁ : HomologicalComplex C₁' c₁) (K₂ : HomologicalComplex C₂' c₂),
    HasMapBifunctor K₁ K₂ F' c]

/-- The comparison morphisms `mapBifunctorComparison τ c K₁ K₂`, as a natural transformation
between the bifunctors `(K₁, K₂) ↦ G(mapBifunctor K₁ K₂ F c)` and
`(K₁, K₂) ↦ mapBifunctor (G₁ K₁) (G₂ K₂) F' c`. -/
noncomputable def mapBifunctorComparisonNatTrans :
    (Functor.postcompose₂.obj (G.mapHomologicalComplex c)).obj
        (F.map₂HomologicalComplex c₁ c₂ c) ⟶
      (((Functor.whiskeringLeft₂ _).obj (G₁.mapHomologicalComplex c₁)).obj
        (G₂.mapHomologicalComplex c₂)).obj (F'.map₂HomologicalComplex c₁ c₂ c) where
  app K₁ :=
    { app K₂ := mapBifunctorComparison τ c K₁ K₂
      naturality _ _ f₂ := by
        simpa using mapBifunctorComparison_naturality τ c (𝟙 K₁) f₂ }
  naturality _ _ f₁ := by
    ext K₂ : 2
    simpa using mapBifunctorComparison_naturality τ c f₁ (𝟙 K₂)

@[simp]
lemma mapBifunctorComparisonNatTrans_app_app (K₁ : HomologicalComplex C₁ c₁)
    (K₂ : HomologicalComplex C₂ c₂) :
    ((mapBifunctorComparisonNatTrans τ c).app K₁).app K₂ = mapBifunctorComparison τ c K₁ K₂ :=
  rfl

instance [∀ X₁ X₂, IsIso ((τ.app X₁).app X₂)] (K₁ : HomologicalComplex C₁ c₁)
    (K₂ : HomologicalComplex C₂ c₂) :
    IsIso (((mapBifunctorComparisonNatTrans τ c).app K₁).app K₂) :=
  inferInstanceAs (IsIso (mapBifunctorComparison τ c K₁ K₂))

instance [∀ X₁ X₂, IsIso ((τ.app X₁).app X₂)] (K₁ : HomologicalComplex C₁ c₁) :
    IsIso ((mapBifunctorComparisonNatTrans (c₂ := c₂) τ c).app K₁) :=
  NatIso.isIso_of_isIso_app _

instance [∀ X₁ X₂, IsIso ((τ.app X₁).app X₂)] : 
    IsIso (mapBifunctorComparisonNatTrans (c₁ := c₁) (c₂ := c₂) τ c) :=
  NatIso.isIso_of_isIso_app _

end

end HomologicalComplex
