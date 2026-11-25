/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageSectionUnit
public import WeilConjectures.AlgebraicGeometry.Square.SquareResolutionRoofModels

/-! # The injective endpoint comparison preserves the section unit

Source: Stacks Project, Cohomology, Tags 079V and 0D5X.
(blueprint: lem-weil-pbc-injective-section-unit-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
private theorem augmentation_unit_algebra {C D E : Type*}
    [Category C] [Category D] [Category E] (R T : C ⥤ D) (L : R ⟶ T)
    {A B : C} (r : A ≅ B) {K : D} (z : R.obj B ≅ K) (Ev : D ⥤ E)
    {N : E} (a : N ⟶ Ev.obj K) :
    a ≫ Ev.map z.inv ≫ Ev.map (R.map r.inv) ≫ Ev.map (L.app A) ≫
        Ev.map (T.map r.hom) = a ≫ Ev.map z.inv ≫ Ev.map (L.app B) := by
  have hn : R.map r.inv ≫ L.app A ≫ T.map r.hom = L.app B := by
    rw [reassoc_of% (L.naturality r.inv)]
    simp only [← T.map_comp, Iso.inv_hom_id, T.map_id, Category.comp_id]
  simpa only [Ev.map_comp, Category.assoc] using
    congrArg (fun t ↦ a ≫ Ev.map z.inv ≫ Ev.map t) hn

attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory Scheme.Modules.instAbelian TopCat.Sheaf

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The raw injective comparison followed by the augmentation is the cochain section unit.
There is one direct image and one injective resolution, and no coefficient map or square.
Source: Stacks Project, Tags 079V and 0D5X
(blueprint: lem-weil-pbc-injective-section-unit-comparison).

Proof: Extend I by zero; its lower bound and termwise injectivity make it
K-injective. Put r = asIso(Q(I.ι')), R = inverse-open hypercohomology and
T = local hypercohomology after Rf_*. The unique unit-preserving natural comparison
l : R ⟶ T has component the inverse of topEdgeLocalLeray. Let z be homology of the
inverse-open model comparison on the extended I followed by homologyFunctorFactors.
The cochain inverse-open unit at I is the inverse model comparison. Unfolding
squareInjectiveLocalComparison gives the exact evaluation/homology comparison,
then evaluation of z inverse, R(r inverse), and l at F[0]. Postcompose by T(r).
Naturality of l at r inverse cancels T(r inverse) followed by T(r). What remains
is exactly directImageSectionUnitAt on I. The degree-zero single-complex comparison
is reflexive, so its identity transport cancels as well. These equations also
apply to zero resolutions, degree zero and empty opens. -/
theorem injectiveSectionUnit_comparison {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (q : ℕ) (V : S.Opens) (I : InjectiveResolution F) :
    (squareInjectiveLocalComparison f F q V I (f ⁻¹ᵁ V) rfl).hom ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        ((schemeDerivedDirectImage f).map (DerivedCategory.Q.map I.ι'))).app (op V) =
      directImageSectionUnitAt f (q : ℤ) V I.cochainComplex := by
  dsimp only [Scheme.Modules, Scheme.Modules.Hom, Scheme.Modules.instCategory] at *
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections S.toRingedSpace
  let E := (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let H := DerivedCategory.homologyFunctor (S.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (q : ℤ)
  let R := RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom (q : ℤ)
  let T := schemeDerivedDirectImage f ⋙
    RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)
  let l := RingedSpace.directImageSectionComparison f.toLRSHom.toShHom (q : ℤ)
  let : I.cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective I.cochainComplex 0
  let r : (DerivedCategory.singleFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F ≅
      DerivedCategory.Q.{w, u, u + 1}.obj I.cochainComplex :=
    asIso (DerivedCategory.Q.{w, u, u + 1}.map I.ι')
  let z : R.obj (DerivedCategory.Q.{w, u, u + 1}.obj I.cochainComplex) ≅
      ((P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (q : ℤ) :=
    H.mapIso (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace) (𝟙 I.cochainComplex)) ≪≫
      (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _
  have hh := augmentation_unit_algebra R T l r z E
    (((((P.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).sc
      (q : ℤ)).mapHomologyIso E).hom)
  unfold squareInjectiveLocalComparison directImageSectionUnitAt directImageSectionUnit
  dsimp only [id]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_inv, Iso.app_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [RingedSpace.inverseOpenUnitQ_model]
  simp only [← RingedSpace.directImageSectionComparison_eq]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv,
    NatTrans.id_app]
  erw [Category.comp_id]
  simpa only [R, T, l, r, z, H, E, P, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, asIso_inv, asIso_hom,
    DerivedCategory.singleFunctorIsoCompQ, NatTrans.id_app, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Functor.map_comp, NatTrans.comp_app,
    CategoryTheory.evaluation_obj_map, Functor.comp_map, Category.assoc] using hh

end AlgebraicGeometry
