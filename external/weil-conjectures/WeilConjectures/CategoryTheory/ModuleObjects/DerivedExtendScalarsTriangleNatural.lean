/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit

/-!

# The natural reduction triangle of the derived extension of scalars

Let `φ : R ⟶ S` be a morphism of commutative algebra objects such that
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, and write `T = L(Ext_φ) ⋙ D(Res_φ)` for the
monad of the derived adjunction `L(Ext_φ) ⊣ D(Res_φ)`, with unit `η : 𝟭 ⟶ T`. This file
constructs a *natural* transformation `δ : T ⟶ [1]` (`Mod.derivedExtendScalarsTriangleδ`) such
that for every `K ∈ D(Mod_R(C))` the triangle
```
K --k--> K --η_K--> T K --δ_K--> K[1]
```
is distinguished (`Mod.derivedExtendScalarsTriangle_distinguished`). This upgrades the existence
statement `Mod.exists_distinguished_zsmul_derivedExtendMapDerivedCategoryUnit`, whose connecting
morphism is not functorial in `K`.

On a complex `K` the connecting morphism is computed on the chosen functorial K-flat resolution
`ρ K ⟶ K` (`CochainComplex.flatResolutionFunctor`): the sequence
`0 ⟶ ρ K --k--> ρ K ⟶ S ⊗_R ρ K ⟶ 0` is a short exact sequence of complexes, natural in `K`,
and its connecting morphism `DerivedCategory.triangleOfSESδ` is natural for morphisms of short
exact sequences (`DerivedCategory.triangleOfSESδ_naturality`). The resulting natural
transformation on complexes descends to the derived category along the localization `Q`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

/-! ### A chosen functorial K-flat resolution -/

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

/-- The chosen functorial flat resolution data of `C`. -/
noncomputable abbrev flatResolutionData : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) :=
  (Classical.arbitrary (Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C))).reduced

/-- The chosen functorial K-flat resolution `ρ` of complexes by complexes of flat objects. -/
noncomputable abbrev flatResolutionFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  (flatResolutionData C).resolutionFunctor

/-- The augmentation `ρ ⟶ 𝟭` of the functorial K-flat resolution. -/
noncomputable abbrev flatResolutionπ : flatResolutionFunctor C ⟶ 𝟭 _ :=
  (flatResolutionData C).resolutionNatTrans

variable {C}

instance quasiIso_flatResolutionπ_app (L : CochainComplex C ℤ) :
    QuasiIso ((flatResolutionπ C).app L) :=
  inferInstanceAs (QuasiIso ((flatResolutionData C).resolutionNatTrans.app L))

/-- The functorial resolution of a complex is K-flat. -/
lemma kFlat_flatResolutionFunctor_obj (L : CochainComplex C ℤ) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat ((flatResolutionFunctor C).obj L) := by
  have (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  exact (flatResolutionData C).kFlat_resolutionFunctor_obj hι L

/-- The functorial resolution of a complex consists of flat objects. -/
lemma flat_flatResolutionFunctor_obj_X (L : CochainComplex C ℤ) (n : ℤ) :
    ObjectProperty.flat (((flatResolutionFunctor C).obj L).X n) := by
  have (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  have hι : (ObjectProperty.flat.ι : _ ⥤ C).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  have := CochainComplex.closedUnderColimitsOfShape_flat C ℤ
  let c := (flatResolutionData C).colimitOfShapeResolutionFunctorObj L
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n) c.isColimit)
    (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))

end CochainComplex

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The levelwise reduction functor `P ↦ S ⊗_R P` on complexes of `R`-modules, regarded as
complexes of `R`-modules. -/
noncomputable abbrev extendComapComplexFunctor :
    CochainComplex (Mod C R) ℤ ⥤ CochainComplex (Mod C R) ℤ :=
  (extendScalars φ ⋙ comap φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The comparison `T (Qh P) ⟶ Qh (S ⊗_R P)` of the monad `T = L(Ext_φ) ⋙ D(Res_φ)` with the
levelwise extension of scalars, at the level of the homotopy category: the counit of the left
derived functor, followed by the comparison for the exact restriction of scalars. It is an
isomorphism on K-flat complexes. -/
noncomputable def derivedExtendComapComparisonh (P : CochainComplex (Mod C R) ℤ) :
    (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        ((extendComapComplexFunctor φ).obj P)) :=
  (comap φ).mapDerivedCategory.map
      ((extendScalars φ).leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
    (comap φ).mapDerivedCategoryFactorsh.hom.app
      (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P))

/-- The comparison `T (Q P) ⟶ Q (S ⊗_R P)` of the monad `T = L(Ext_φ) ⋙ D(Res_φ)` with the
levelwise extension of scalars. It is an isomorphism on K-flat complexes. -/
noncomputable def derivedExtendComapComparison (P : CochainComplex (Mod C R) ℤ) :
    (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj
        (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((extendComapComplexFunctor φ).obj P) :=
  (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P)) ≫
    derivedExtendComapComparisonh φ P ≫
    (DerivedCategory.quotientCompQhIso (Mod C R)).hom.app ((extendComapComplexFunctor φ).obj P)

/-- The comparison `T (Qh P) ⟶ Qh (S ⊗_R P)` is natural in the complex `P`. -/
@[reassoc]
lemma derivedExtendComapComparisonh_naturality {P P' : CochainComplex (Mod C R) ℤ}
    (f : P ⟶ P') :
    (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f))) ≫
        derivedExtendComapComparisonh φ P' =
      derivedExtendComapComparisonh φ P ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ _).map ((extendComapComplexFunctor φ).map f)) := by
  have h₁ := (extendScalars φ).leftDerivedFunctorCounit.naturality
    ((HomotopyCategory.quotient _ _).map f)
  have h₂ := (comap φ).mapDerivedCategoryFactorsh.hom.naturality
    (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient _ _).map f))
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  simp only [derivedExtendComapComparisonh, ← Functor.map_comp_assoc, h₁]
  rw [Functor.map_comp, Category.assoc, h₂, Category.assoc, Functor.mapHomotopyCategory_map,
    Functor.mapHomotopyCategory_map]
  rfl

/-- The comparison `T (Q P) ⟶ Q (S ⊗_R P)` is natural in the complex `P`. -/
@[reassoc]
lemma derivedExtendComapComparison_naturality {P P' : CochainComplex (Mod C R) ℤ}
    (f : P ⟶ P') :
    (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (DerivedCategory.Q.map f)) ≫ derivedExtendComapComparison φ P' =
      derivedExtendComapComparison φ P ≫
        DerivedCategory.Q.map ((extendComapComplexFunctor φ).map f) := by
  have h₁ := (DerivedCategory.quotientCompQhIso (Mod C R)).inv.naturality f
  simp only [Functor.comp_obj, Functor.comp_map] at h₁
  have h₂ : (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (DerivedCategory.Q.map f)) ≫ (comap φ).mapDerivedCategory.map
        ((extendScalars φ).leftDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P')) =
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P)) ≫
        (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f))) := by
    simp only [← Functor.map_comp, h₁]
  simp only [derivedExtendComapComparison, Category.assoc]
  rw [reassoc_of% h₂, derivedExtendComapComparisonh_naturality_assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality]

/-- The comparison `T (Q P) ⟶ Q (S ⊗_R P)` sends the unit of the derived adjunction to the
levelwise unit `P ⟶ S ⊗_R P`. -/
@[reassoc]
lemma unit_app_comp_derivedExtendComapComparison (P : CochainComplex (Mod C R) ℤ) :
    (derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Q.obj P) ≫
        derivedExtendComapComparison φ P =
      DerivedCategory.Q.map (extendUnitComplexHom φ P) := by
  have h₁ : (derivedExtendMapDerivedCategoryAdjunction φ).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
        derivedExtendComapComparisonh φ P =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (extendUnitComplexHom φ P)) := by
    rw [extendUnitComplexHom_eq, ← Adjunction.mapHomotopyCategory_unit_app_quotient]
    exact derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ _
  have h₂ := (derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality
    ((DerivedCategory.quotientCompQhIso (Mod C R)).inv.app P)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h₂
  simp only [derivedExtendComapComparison]
  rw [← reassoc_of% h₂, reassoc_of% h₁, DerivedCategory.quotientCompQhIso_hom_naturality,
    Iso.inv_hom_id_app_assoc]

/-- The comparison `T (Q P) ⟶ Q (S ⊗_R P)` is an isomorphism on K-flat complexes. -/
lemma isIso_derivedExtendComapComparison (P : CochainComplex (Mod C R) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (derivedExtendComapComparison φ P) := by
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  dsimp only [derivedExtendComapComparison, derivedExtendComapComparisonh]
  infer_instance

variable {φ} (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0) (hφ : (ShortComplex.mk _ _ w).ShortExact)

/-- The reduction sequence `P --k--> P ⟶ S ⊗_R P` of complexes of `R`-modules, short exact for a
complex of flat modules (`Mod.shortExact_extendUnitComplexHom`). -/
noncomputable abbrev reductionShortComplex (P : CochainComplex (Mod C R) ℤ) :
    ShortComplex (CochainComplex (Mod C R) ℤ) :=
  ShortComplex.mk (k • 𝟙 P) (extendUnitComplexHom φ P) (by
    ext i
    simpa using congrArg Hom.hom (zsmul_comp_extendUnit k w (P.X i)))

/-- The reduction sequence is functorial in the complex. -/
@[simps]
noncomputable def reductionShortComplexMap {P P' : CochainComplex (Mod C R) ℤ} (f : P ⟶ P') :
    reductionShortComplex k w P ⟶ reductionShortComplex k w P' where
  τ₁ := f
  τ₂ := f
  τ₃ := (extendComapComplexFunctor φ).map f
  comm₁₂ := by simp
  comm₂₃ := by
    dsimp only [reductionShortComplex, ShortComplex.mk]
    rw [extendUnitComplexHom_eq, extendUnitComplexHom_eq]
    exact ((extendRestrictAdjunction φ).mapHomologicalComplex _).unit.naturality f

/-- The connecting morphism of the reduction triangle on the image of a complex `K`, computed on
its functorial K-flat resolution `ρ K ⟶ K`. -/
noncomputable def reductionδComplex (K : CochainComplex (Mod C R) ℤ) :
    (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj
        (DerivedCategory.Q.obj K)) ⟶ (DerivedCategory.Q.obj K)⟦(1 : ℤ)⟧ :=
  (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
      (inv (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app K)))) ≫
    derivedExtendComapComparison φ ((CochainComplex.flatResolutionFunctor _).obj K) ≫
    DerivedCategory.triangleOfSESδ (shortExact_extendUnitComplexHom k w hφ _
      (CochainComplex.flat_flatResolutionFunctor_obj_X K)) ≫
    (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app K))⟦(1 : ℤ)⟧'

/-- The connecting morphism of the reduction triangle is natural in the complex. -/
lemma reductionδComplex_naturality {K K' : CochainComplex (Mod C R) ℤ} (g : K ⟶ K') :
    (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (DerivedCategory.Q.map g)) ≫ reductionδComplex k w hφ K' =
      reductionδComplex k w hφ K ≫ (DerivedCategory.Q.map g)⟦(1 : ℤ)⟧' := by
  have hπ := (CochainComplex.flatResolutionπ (Mod C R)).naturality g
  have h₁ : DerivedCategory.Q.map g ≫
      inv (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app K')) =
      inv (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app K)) ≫
        DerivedCategory.Q.map ((CochainComplex.flatResolutionFunctor _).map g) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, ← Functor.map_comp,
      ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map hπ.symm
  have h₂ : (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (DerivedCategory.Q.map g)) ≫
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (inv (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app K')))) =
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (inv (DerivedCategory.Q.map ((CochainComplex.flatResolutionπ _).app K)))) ≫
      (comap φ).mapDerivedCategory.map ((extendScalars φ).leftDerivedFunctor.map
        (DerivedCategory.Q.map ((CochainComplex.flatResolutionFunctor _).map g))) := by
    simp only [← Functor.map_comp, h₁]
  have h₃ := DerivedCategory.triangleOfSESδ_naturality
    (shortExact_extendUnitComplexHom k w hφ _
      (CochainComplex.flat_flatResolutionFunctor_obj_X K))
    (shortExact_extendUnitComplexHom k w hφ _
      (CochainComplex.flat_flatResolutionFunctor_obj_X K'))
    (reductionShortComplexMap k w ((CochainComplex.flatResolutionFunctor _).map g))
  simp only [reductionShortComplexMap_τ₁, reductionShortComplexMap_τ₃] at h₃
  simp only [reductionδComplex, Category.assoc]
  rw [reassoc_of% h₂, derivedExtendComapComparison_naturality_assoc, ← reassoc_of% h₃,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  simp only [Functor.id_obj, Functor.id_map] at hπ
  rw [hπ]

/-- The connecting morphisms of the reduction triangles of complexes, as a natural
transformation. -/
@[simps]
noncomputable def reductionδComplexNatTrans :
    DerivedCategory.Q ⋙ (extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory ⟶
      DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory (Mod C R)) (1 : ℤ) where
  app K := reductionδComplex k w hφ K
  naturality _ _ g := reductionδComplex_naturality k w hφ g

/-- **The connecting morphism of the reduction triangle**: the natural transformation
`δ : L(Ext_φ) ⋙ D(Res_φ) ⟶ [1]` such that `K --k--> K --η_K--> S ⊗ᴸ_R K --δ_K--> K[1]` is a
distinguished triangle for every `K` (`Mod.derivedExtendScalarsTriangle_distinguished`). -/
noncomputable def derivedExtendScalarsTriangleδ :
    (extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory ⟶
      shiftFunctor (DerivedCategory (Mod C R)) (1 : ℤ) :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    _ _ _ _ (reductionδComplexNatTrans k w hφ)

lemma derivedExtendScalarsTriangleδ_app_Q_obj (K : CochainComplex (Mod C R) ℤ) :
    (derivedExtendScalarsTriangleδ k w hφ).app (DerivedCategory.Q.obj K) =
      reductionδComplex k w hφ K := by
  simp [derivedExtendScalarsTriangleδ]

/-- The reduction triangle with the natural connecting morphism is distinguished on the image of
a complex. -/
lemma derivedExtendScalarsTriangle_distinguished_Q_obj (K : CochainComplex (Mod C R) ℤ) :
    Triangle.mk (k • 𝟙 (DerivedCategory.Q.obj K))
        ((derivedExtendMapDerivedCategoryAdjunction φ).unit.app (DerivedCategory.Q.obj K))
        ((derivedExtendScalarsTriangleδ k w hφ).app (DerivedCategory.Q.obj K)) ∈
      distTriang (DerivedCategory (Mod C R)) := by
  let P := (CochainComplex.flatResolutionFunctor (Mod C R)).obj K
  let π := (CochainComplex.flatResolutionπ (Mod C R)).app K
  have hS := shortExact_extendUnitComplexHom k w hφ P
    (CochainComplex.flat_flatResolutionFunctor_obj_X K)
  have := isIso_derivedExtendComapComparison φ P
    (CochainComplex.kFlat_flatResolutionFunctor_obj K)
  let e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K := asIso (DerivedCategory.Q.map π)
  let e₃ : DerivedCategory.Q.obj ((extendComapComplexFunctor φ).obj P) ≅
      (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj
        (DerivedCategory.Q.obj K)) :=
    (asIso (derivedExtendComapComparison φ P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso ((extendScalars φ).leftDerivedFunctor.mapIso e)
  rw [derivedExtendScalarsTriangleδ_app_Q_obj]
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ e e e₃ ?_ ?_ ?_).symm
  · simp only [e, DerivedCategory.triangleOfSES, Triangle.mk_mor₁, asIso_hom, Functor.map_zsmul,
      Functor.map_id, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    erw [Category.id_comp, Category.comp_id]
  · have h := (derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality
      (DerivedCategory.Q.map π)
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h
    simp only [e, e₃, DerivedCategory.triangleOfSES, Triangle.mk_mor₂, Iso.trans_hom, Iso.symm_hom,
      asIso_inv, asIso_hom, Functor.mapIso_hom]
    rw [h, ← unit_app_comp_derivedExtendComapComparison_assoc, IsIso.hom_inv_id_assoc]
  · simp [e, e₃, DerivedCategory.triangleOfSES, reductionδComplex, P, π]

/-- **The natural reduction triangle**: if `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, then
for every `K ∈ D(Mod_R(C))` the triangle `K --k--> K --η_K--> S ⊗ᴸ_R K --δ_K--> K[1]` is
distinguished, where `η` is the unit of `L(Ext_φ) ⊣ D(Res_φ)` and `δ` is the natural
transformation `Mod.derivedExtendScalarsTriangleδ`. -/
theorem derivedExtendScalarsTriangle_distinguished (M : DerivedCategory (Mod C R)) :
    Triangle.mk (k • 𝟙 M) ((derivedExtendMapDerivedCategoryAdjunction φ).unit.app M)
        ((derivedExtendScalarsTriangleδ k w hφ).app M) ∈
      distTriang (DerivedCategory (Mod C R)) := by
  let e := DerivedCategory.Q.objObjPreimageIso M
  refine isomorphic_distinguished _ (derivedExtendScalarsTriangle_distinguished_Q_obj k w hφ
    (DerivedCategory.Q.objPreimage M)) _ (Triangle.isoMk _ _ e.symm e.symm
      ((comap φ).mapDerivedCategory.mapIso ((extendScalars φ).leftDerivedFunctor.mapIso e.symm))
      ?_ ?_ ?_)
  · simp only [Triangle.mk_mor₁, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    erw [Category.id_comp, Category.comp_id]
  · exact ((derivedExtendMapDerivedCategoryAdjunction φ).unit.naturality e.inv).symm
  · exact ((derivedExtendScalarsTriangleδ k w hφ).naturality e.inv).symm

end CategoryTheory.Mod
