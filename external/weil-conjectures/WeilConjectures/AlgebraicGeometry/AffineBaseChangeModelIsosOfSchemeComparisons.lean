/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineModelComparisonData
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.AffineSquareKFlatModelIso
import WeilConjectures.AlgebraicGeometry.AffineModelComparisonOfBottomModels
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem module_model_acyclic
    (A : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : L.Acyclic) :
    (CochainComplex.mapBifunctor L M
      (MonoidalCategory.curriedTensor (ModuleCat.{u} A))).Acyclic := by
  have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
    ((HomotopyCategory.quotient _ (.up ℤ)).obj M)).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff M).mpr hM)
  have hL' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).mpr hL
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
    (h _ hL').2

/-- Core categorical construction.
Source: Stacks Project Tags 08DW, 09RE and 0D5S.
Proof: use affine K-flat pullback naturality and scalar-extension associativity.
(blueprint: lem-pc-affine-base-change-model-isos-core).
-/
theorem affineBaseChangeModelIsosCore
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y)
    (e : schemeDerivedCategory (Spec (Scheme.Γ.obj (.op Y))) ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward t.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (P Q : schemeDerivedCategory Y)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (Scheme.Γ.obj (.op Y))) ℤ)
    (hE : (HomologicalComplex.quasiIso (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
      (.up ℤ)).kFlat E₀)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
      (.up ℤ)).kFlat K₀)
    (hPE : e.inverse.obj P ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E₀))
    (hQK : e.inverse.obj Q ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K₀))
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (r : Scheme.Γ.obj (.op Y) →+* F.obj ⟨i, le_rfl⟩)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hEr : E = ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀)
    (hKr : K = ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀)
    (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))))
    (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i)))
    (hgeom :
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        (σ j).hom ≫ pullback.fst s (Spec.map (R.map (homOfLE j.val.property))) =
          Spec.map (CommRingCat.ofHom r ≫ F.map (homOfLE j.property)) ≫ t.hom) ∧
      (τ.hom ≫ pullback.fst s (Spec.map (c.ι.app i)) =
        Spec.map (CommRingCat.ofHom r ≫ C.ι.app ⟨i, le_rfl⟩) ≫ t.hom) ∧
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
        (σ k).hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) =
          Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        τ.hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j.val))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) =
          Spec.map (C.ι.app j.val) ≫ (σ j).hom))
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      DerivedCategory.Q ⋙ (d j).functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace))
        (SheafOfModules.{u}
          (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace))
        _ _ _ _
        (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace))
        (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward τ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    Nonempty (affineModelComparisonData R c i Y s P Q F C E K) := by
  subst E
  subst K
  let j₀ : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) := ⟨⟨i, le_rfl⟩, le_rfl⟩
  have hsquare : (σ j₀).hom ≫
      pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))) =
        Spec.map (CommRingCat.ofHom r) ≫ t.hom := by
    have hb := hgeom.1 j₀
    change (σ j₀).hom ≫ _ =
      Spec.map (CommRingCat.ofHom r ≫ F.map (𝟙 (⟨i, le_rfl⟩ : Set.Ici i))) ≫ t.hom at hb
    have hid : CommRingCat.ofHom r ≫ F.map (𝟙 (⟨i, le_rfl⟩ : Set.Ici i)) =
        CommRingCat.ofHom r := by
      rw [F.map_id]
      exact Category.comp_id _
    rw [hid] at hb
    exact hb
  obtain ⟨aE⟩ := nonempty_affineSquareKFlatModelIso
    (Scheme.Γ.obj (.op Y)) (F.obj ⟨i, le_rfl⟩) Y _ t (σ j₀) r
    (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))
    hsquare e (d j₀) he (hd j₀) E₀ hE P hPE
  obtain ⟨aK⟩ := nonempty_affineSquareKFlatModelIso
    (Scheme.Γ.obj (.op Y)) (F.obj ⟨i, le_rfl⟩) Y _ t (σ j₀) r
    (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))
    hsquare e (d j₀) he (hd j₀) K₀ hK Q hQK
  have hE' := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat r E₀
    (module_model_acyclic _ E₀ hE)
  have hK' := CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat r K₀
    (module_model_acyclic _ K₀ hK)
  exact ⟨affineModelComparisonData_of_bottom_models R c i Y s P Q F C _ _
    hE' hK' σ τ ⟨hgeom.2.2.1, hgeom.2.2.2⟩ d dlim hd hdlim aE aK⟩


/-- (blueprint: lem-pc-affine-base-change-model-isos-of-scheme-comparisons) -/
theorem exists_affineBaseChangeModelIsosOfSchemeComparisons
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y)
    (e : schemeDerivedCategory (Spec (Scheme.Γ.obj (.op Y))) ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward t.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (P Q : schemeDerivedCategory Y)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (Scheme.Γ.obj (.op Y))) ℤ)
    (hE : (HomologicalComplex.quasiIso (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
      (.up ℤ)).kFlat E₀)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
      (.up ℤ)).kFlat K₀)
    (hPE : e.inverse.obj P ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E₀))
    (hQK : e.inverse.obj Q ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K₀))
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (r : Scheme.Γ.obj (.op Y) →+* F.obj ⟨i, le_rfl⟩)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hEr : E = ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀)
    (hKr : K = ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀)
    (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))))
    (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i)))
    (hgeom :
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        (σ j).hom ≫ pullback.fst s (Spec.map (R.map (homOfLE j.val.property))) =
          Spec.map (CommRingCat.ofHom r ≫ F.map (homOfLE j.property)) ≫ t.hom) ∧
      (τ.hom ≫ pullback.fst s (Spec.map (c.ι.app i)) =
        Spec.map (CommRingCat.ofHom r ≫ C.ι.app ⟨i, le_rfl⟩) ≫ t.hom) ∧
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
        (σ k).hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) =
          Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        τ.hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j.val))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) =
          Spec.map (C.ι.app j.val) ≫ (σ j).hom))
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      DerivedCategory.Q ⋙ (d j).functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace))
        (SheafOfModules.{u}
          (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace))
        _ _ _ _
        (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace))
        (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward τ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    affineModelComparisonData R c i Y s P Q F C E K := by
  exact (affineBaseChangeModelIsosCore (R := R) (c := c) (i := i) (Y := Y)
    (s := s) (t := t) (e := e) (he := he) (P := P) (Q := Q) (E₀ := E₀) (K₀ := K₀)
    (hE := hE) (hK := hK) (hPE := hPE) (hQK := hQK) (F := F) (C := C) (r := r)
    (E := E) (K := K) (hEr := hEr) (hKr := hKr) (σ := σ) (τ := τ) (hgeom := hgeom)
    (d := d) (dlim := dlim) (hd := hd) (hdlim := hdlim)).some


end AlgebraicGeometry
