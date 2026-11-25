/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionAffineModel

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The mapping/extension comparison preserves the identified nonzero terms. -/
@[reassoc] theorem tensorResolutionMapExtendIso_f
    {C : Type u} {D : Type v} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex C c)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (tensorResolutionMapExtendIso F e K).hom.f i' ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom =
      F.map (K.extendXIso e h).hom := by
  let eX (o : Option ι) :
      F.obj (HomologicalComplex.extend.X K o) ≅
        HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) o :=
    match o with
    | none => (F.map_isZero (isZero_zero C)).iso (isZero_zero D)
    | some _ => Iso.refl _
  have aux (o : Option ι) (ho : o = some i) :
      (eX o).hom ≫ (HomologicalComplex.extend.XIso
          ((F.mapHomologicalComplex c).obj K) ho).hom =
        F.map (HomologicalComplex.extend.XIso K ho).hom := by
    subst o
    simp [eX, HomologicalComplex.extend.XIso]
  exact aux (e.r i') (e.r_eq_some h)

/-- Extend a semilinear complex map by zero. -/
noncomputable def tensorResolutionExtendSemilinear
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex c).obj F) :
    E.extend e ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex c').obj (F.extend e) :=
  HomologicalComplex.extendMap a e ≫
    (tensorResolutionMapExtendIso (ModuleCat.restrictScalars φ) e F).inv

/-- On the original degrees, extension of a semilinear map is the supplied map. -/
@[reassoc] theorem tensorResolutionExtendSemilinear_f
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex c).obj F)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (tensorResolutionExtendSemilinear φ e E F a).f i' =
      (E.extendXIso e h).hom ≫ a.f i ≫
        (ModuleCat.restrictScalars φ).map (F.extendXIso e h).inv := by
  dsimp only [tensorResolutionExtendSemilinear, HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f a e h]
  let U := ModuleCat.restrictScalars φ
  have ht := tensorResolutionMapExtendIso_f U e F h
  have hi : ((((U.mapHomologicalComplex c).obj F).extendXIso e h).inv) ≫
      (tensorResolutionMapExtendIso U e F).inv.f i' =
    U.map (F.extendXIso e h).inv := by
    apply (cancel_mono (U.map (F.extendXIso e h).hom)).1
    rw [Category.assoc, ← ht]
    simp only [← Category.assoc, ← HomologicalComplex.comp_f,
      Iso.inv_hom_id, HomologicalComplex.id_f, Category.id_comp, Iso.inv_hom_id]
    rw [Category.assoc, ht, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    rfl
  rw [Category.assoc, Category.assoc, hi]

end AlgebraicGeometry
