/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarPullbackData
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginRestrictionPullbackCube
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginExtensionPullbackCube
import all WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection

/-! # Intrinsic realization and scalar pullback coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Etale.scalarTensorIso Scheme.completedAdicDerivedChange
attribute [local implicit_reducible] properOriginEtaleTensor

private theorem conjugate_tensor_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X X' : C} {Y Y' : D} (e : X ≅ X') (d : Y ≅ Y')
    (f : F.obj X ⟶ Y) (g : F.obj X' ⟶ Y')
    (h : f ≫ d.hom = F.map e.hom ≫ g) :
    F.map e.inv ≫ f = g ≫ d.inv := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, d.inv_hom_id, Category.comp_id]
  rw [h, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

/-- The local scalar/tensor square commutes with the etale-origin pullback comparison.
This involves only left-adjoint operations on an arbitrary unbounded input C.

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 (pullback of derived tensor),
Tag 0B56 (the projection is the counit transpose), and Tag 0E48 (compatibility of
canonical comparisons); modules on sites, Tag 03EL.
(blueprint: lem-fix-etale-origin-scalar-pullback-square).

Proof: expand properOriginTensorIso into its inverse etale scalar/tensor
comparison, inverse realization/restriction comparison and inverse scalar-extension
site comparison. Naturality moves the site comparison past restriction/pullback.
The extension cube and the restriction cube identify the resulting two faces.
Naturality of originPullback and properOriginRestrictionIso moves the remaining
etale scalar-pullback arrows together. The proved scalar_tensor_pullback_square,
conjugated by the two inverse scalar/tensor comparisons, gives the tensor face.
Functoriality composes these equalities. Thus the only new obligations are the
two tensor-free realization cubes, separately about restriction and extension.
-/
theorem etaleOriginScalarPullbackSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (C : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y) :
    (Scheme.proEtaleConstantRingDerivedPullback A p).map (properOriginTensorIso φ Y C).hom ≫
      (originScalarPullback φ p).app
        ((finiteCoefficientIntrinsicDerivedComparison Y A).obj C) ≫
      (directImageScalarExtension φ Z ⋙ (scalarMateRestriction φ Z).mapDerivedCategory).map
        ((originPullback A p).app C) =
    (originPullback A p).app
        (properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y C) ≫
      (finiteCoefficientIntrinsicDerivedComparison Z A).map
        ((originEtaleTensorPullback (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).app C) ≫
      (properOriginTensorIso φ Z
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).leftDerivedFunctor.obj
          C)).hom  := by
  let a := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let F := finiteCoefficientIntrinsicDerivedComparison Z A
  let U := (scalarMateRestriction φ Z).mapDerivedCategory
  let Le := (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).leftDerivedFunctor
  have hr := etaleOriginRestrictionPullbackCube φ p ((Etale.scalarExtension a Y).obj C)
  have hs := congrArg (fun f ↦ U.map f) (etaleOriginExtensionPullbackCube φ p C)
  simp only [Functor.map_comp] at hs
  have hn := (originRestrictionPullback φ p).naturality
    ((Scheme.FiniteCompactScalar.siteScalarIso φ Y).inv.app C)
  dsimp only [Functor.comp_map] at hn
  have he := Etale.scalar_tensor_pullback_square a p C
  have he' : Le.map ((Etale.scalarTensorIso a Y).inv.app C) ≫
      (Etale.scalarRestrictionPullbackIso a p).hom.app
        ((Etale.scalarExtension a Y).obj C) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology a).map
        ((Etale.scalarPullbackIso a p).hom.app C) =
      (originEtaleTensorPullback a p).app C ≫
        (Etale.scalarTensorIso a Z).inv.app (Le.obj C) := by
    apply conjugate_tensor_square Le ((Etale.scalarTensorIso a Y).app C)
      ((Etale.scalarTensorIso a Z).app (Le.obj C))
    simpa only [Le, Functor.comp_obj, Iso.app_hom, Category.assoc,
      originEtaleTensorPullback, NatTrans.comp_app,
      Etale.derivedTensorRightCompLeftDerivedUpperStarIso, NatIso.ofComponents_hom_app,
      Etale.leftDerivedUpperStarTensorIso_hom, Functor.whiskerLeft_app,
      Functor.flip_map_app] using he
  have hnq := (originPullback A p).naturality ((Etale.scalarTensorIso a Y).inv.app C)
  dsimp only [Functor.comp_map] at hnq
  have hnr := (properOriginRestrictionIso φ Z).inv.naturality
    ((Etale.scalarPullbackIso a p).hom.app C)
  dsimp only [Functor.comp_map] at hnr
  simp only [properOriginTensorIso, properOriginScalarTensorImage, originScalarPullback,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [hs]
  rw [reassoc_of% hr]
  rw [reassoc_of% hnq]
  rw [← reassoc_of% hnr]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  simp only [Category.assoc]
  rw [he', F.map_comp]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale
