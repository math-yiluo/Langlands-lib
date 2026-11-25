/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.Abelian.RightDerived.ResolutionNaturality

/-! # Naturality of the comparison for an exact inner functor

Source: Stacks Project, Derived Categories, Tag 015E, applied to the image of an
injective resolution under an exact functor.
(blueprint: new-finite-cover-derived-comparison-natural)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory.Functor

open CategoryTheory Limits

variable {C : Type u₁} {D : Type u₂} {A : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} A]
  [Abelian C] [Abelian D] [Abelian A]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (E : C ⥤ D) (F : D ⥤ A) [E.Additive] [F.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E] [PreservesFiniteLimits F]
  (hE : ∀ (I : C) [Injective I], F.rightAcyclic (E.obj I))

/-- The canonical composite-derived comparison is natural in the resolved object.

Source: Stacks Project, Tag 015E. Lift a morphism to injective resolutions.
The image of this lift under `E` is compatible with the mapped augmentations.
Naturality of the acyclic-resolution comparison identifies its homology map with
`R^q F` of the image morphism. Naturality for the original injective resolutions,
and for the reassociation of termwise functors, gives the claimed square.
(blueprint: new-finite-cover-derived-comparison-natural) -/
theorem compRightDerivedObjIso_hom_naturality {X Y : C} (g : X ⟶ Y) (q : ℕ) :
    ((E ⋙ F).rightDerived q).map g ≫ (compRightDerivedObjIso E F hE q Y).hom =
      (compRightDerivedObjIso E F hE q X).hom ≫ (F.rightDerived q).map (E.map g) := by
  let I := injectiveResolution X
  let J := injectiveResolution Y
  let φ := InjectiveResolution.desc g J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero g J I
  have hmap : E.mapResolution I.ι ≫ (E.mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ D).map (E.map g) ≫ E.mapResolution J.ι := by
    dsimp only [mapResolution]
    rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
      Functor.map_comp, ← Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ (E.mapHomologicalComplex _).map J.ι)
        ((HomologicalComplex.singleMapHomologicalComplex E
          (ComplexShape.up ℕ) 0).inv.naturality g).symm
  have hEφ : (E.mapResolution I.ι).f 0 ≫
      ((E.mapHomologicalComplex _).map φ).f 0 =
        E.map g ≫ (E.mapResolution J.ι).f 0 := by
    simpa using congrArg (fun k ↦ k.f 0) hmap
  have hF := F.rightDerivedObjIsoOfResolution_hom_naturality
    (E.mapResolution I.ι) (E.mapResolution J.ι)
    (fun n ↦ hE (I.cocomplex.X n)) (fun n ↦ hE (J.cocomplex.X n))
    (E.map g) ((E.mapHomologicalComplex _).map φ) hEφ q
  have hI := InjectiveResolution.isoRightDerivedObj_hom_naturality
    g I J φ hφ (E ⋙ F) q
  change ((E ⋙ F).rightDerived q).map g ≫
      ((J.isoRightDerivedObj (E ⋙ F) q).hom ≫
        ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).mapIso
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F))
            (ComplexShape.up ℕ)).symm.app J.cocomplex)).hom ≫
        (F.rightDerivedObjIsoOfResolution (E.mapResolution J.ι)
          (fun n ↦ hE (J.cocomplex.X n)) q).inv) =
    ((I.isoRightDerivedObj (E ⋙ F) q).hom ≫
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F))
          (ComplexShape.up ℕ)).symm.app I.cocomplex)).hom ≫
      (F.rightDerivedObjIsoOfResolution (E.mapResolution I.ι)
        (fun n ↦ hE (I.cocomplex.X n)) q).inv) ≫ (F.rightDerived q).map (E.map g)
  rw [← cancel_mono (F.rightDerivedObjIsoOfResolution (E.mapResolution J.ι)
    (fun n ↦ hE (J.cocomplex.X n)) q).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hF, Iso.inv_hom_id_assoc, ← Category.assoc, hI]
  simp only [Category.assoc]
  congr 1
  simpa only [Functor.map_comp, Functor.comp_map, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_comp,
    Iso.app, Iso.symm_hom] using
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).congr_map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F))
        (ComplexShape.up ℕ)).inv.naturality φ)

end CategoryTheory.Functor
