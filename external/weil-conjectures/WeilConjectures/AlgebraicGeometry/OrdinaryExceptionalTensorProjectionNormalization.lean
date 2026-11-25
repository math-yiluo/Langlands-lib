/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryExceptionalScalarTensorData
public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.AlgebraicGeometry.OrdinaryExceptionalScalarCoefficientPullback
import WeilConjectures.AlgebraicGeometry.OrdinaryExceptionalScalarTensorData

/-! Ordered constant-tensor normalization of the inverse coefficient comparison.
Source: Zheng, Construction 2.26; the normalized proper coefficient projection formula
(blueprint: lem-sfb-ordinary-exceptional-tensor-projection-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Transport of the ordered proper projection map along the constant coefficient model:
if the coefficient identifications `B_Y[0] ≅ (B[0])_Y` and `B_Z[0] ≅ (B[0])_Z` are
compatible with the two pullback identifications, then the scalar-coefficient ordered
projection map, followed by these identifications, is the ordered constant projection
isomorphism `properConstantProjectionIso` for the constant complex `B[0]`.
Source: the projection clause of properFiniteCoefficientExtension and Zheng,
Construction 2.26
(blueprint: lem-sfb-ordinary-exceptional-tensor-projection-normalization).

Proof: naturality of the signed derived symmetry and of the projection map in the
coefficient, followed by the assumed compatibility of the pullback identifications. -/
theorem ordinaryExceptional_orderedProjection_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (h : (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
        (ordinaryScalarCoefficientIso φ Y).hom ≫
      ((constantFunctorCompLeftDerivedUpperStarIso A p).app
        (ordinaryCoefficientComplex φ)).hom =
      (scalarCoefficientPullbackIso φ p).hom ≫ (ordinaryScalarCoefficientIso φ Z).hom)
    (K : DerivedCategoryModule A Z) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map (ordinaryScalarCoefficientIso φ Y).hom).app
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K) ≫
      (properConstantProjectionIso A p (ordinaryCoefficientComplex φ) K).hom =
    ordinaryScalarProjectionMap φ p K ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
        (((derivedTensor (ModuleCat.{u + 1} A) Z).map
          (ordinaryScalarCoefficientIso φ Z).hom).app K) := by
  have hP : ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K)).map
          (ordinaryScalarCoefficientIso φ Y).hom ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app K).app _ =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app K).app _ ≫
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
            ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
              (ordinaryScalarCoefficientIso φ Y).hom)) :=
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app K).naturality _
  have hX : ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
          (ordinaryScalarCoefficientIso φ Y).hom) ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app K).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).map
          ((constantFunctorCompLeftDerivedUpperStarIso A p).hom.app
            (ordinaryCoefficientComplex φ))).app K =
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
          (scalarCoefficientPullbackIso φ p).hom ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app K).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} A) Z).map
            (ordinaryScalarCoefficientIso φ Z).hom).app K := by
    rw [Iso.app_hom] at h
    rw [NatTrans.naturality_assoc, NatTrans.naturality_assoc, Functor.flip_obj_map,
      Functor.flip_obj_map, ← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp,
      ← Functor.map_comp, h]
  simp only [properConstantProjectionIso, ordinaryScalarProjectionMap, Iso.trans_hom,
    Iso.app_hom, asIso_hom, Functor.mapIso_hom, Category.assoc]
  erw [NatTrans.naturality_app_assoc, Functor.flip_map_app, reassoc_of% hP]
  simp only [← Functor.map_comp, Category.assoc]
  erw [hX]

/-- Under the canonical scalar/constant-tensor identifications, the restricted inverse
proper coefficient comparison is the inverse ordered constant projection.

Source: the projection clause of properFiniteCoefficientExtension and Zheng,
Construction 2.26
(blueprint: lem-sfb-ordinary-exceptional-tensor-projection-normalization).

Proof: apply the projection equation for scalarMate, and cancel its two tensor symmetry
isomorphisms. Express the coefficient object B as the constant sheaf of its restricted
A-module, commute the constant functor with the degree-zero embedding, and use naturality
of the derived tensor and pullback comparisons. The resulting forward comparison is
properConstantProjectionIso conjugated by ordinaryScalarTensorIso. Invert the equality
of isomorphisms, substitute q.hom = scalarMate, and cancel the scalar tensor comparison
at the source. This gives the displayed inverse comparison in the required order. -/
theorem ordinaryExceptional_tensorProjection_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p] [IsIso (scalarRestrictionDirectImageMap φ p)]
    (q : (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor ⋙ scalarExtension φ Y ≅
      scalarExtension φ Z ⋙ (lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor)
    (hq : q.hom = scalarMate φ p) (K : DerivedCategoryModule A Z) :
    (inv (scalarRestrictionDirectImageMap φ p)).app ((scalarExtension φ Z).obj K) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map (q.inv.app K) ≫
        (ordinaryScalarTensorIso φ Y).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K) =
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
          ((ordinaryScalarTensorIso φ Z).hom.app K) ≫
        (properConstantProjectionIso A p (ordinaryCoefficientComplex φ) K).inv := by
  let F := (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor
  let U := Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ
  let bY := scalarTensorIso φ Y ≪≫
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).app (scalarCoefficient φ Y)).symm
  let bZ := scalarTensorIso φ Z ≪≫
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).app (scalarCoefficient φ Z)).symm
  have hb : bY.inv.app (F.obj K) ≫ U.map (q.hom.app K) ≫
      (scalarRestrictionDirectImageMap φ p).app ((scalarExtension φ Z).obj K) ≫
      F.map (bZ.hom.app K) = ordinaryScalarProjectionMap φ p K := by
    rw [hq]
    simpa only [bY, bZ, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      NatTrans.comp_app, Iso.app_hom, Iso.app_inv, ordinaryScalarProjectionMap,
      ← ordinaryTensorSymmetry_swap, F, U, Category.assoc] using
      (properFiniteCoefficientExtension φ p).2.1 K
  have ht := ordinaryExceptional_orderedProjection_transport φ p
    (ordinaryExceptional_scalarCoefficient_pullback φ p) K
  have heY (J : DerivedCategoryModule A Y) :
      (ordinaryScalarTensorIso φ Y).hom.app J = bY.hom.app J ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map
          (ordinaryScalarCoefficientIso φ Y).hom).app J := by
    simp only [ordinaryScalarTensorIso, bY, Iso.trans_hom, NatTrans.comp_app,
      Functor.mapIso_hom, Category.assoc]
  have heZ (J : DerivedCategoryModule A Z) :
      (ordinaryScalarTensorIso φ Z).hom.app J = bZ.hom.app J ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).map
          (ordinaryScalarCoefficientIso φ Z).hom).app J := by
    simp only [ordinaryScalarTensorIso, bZ, Iso.trans_hom, NatTrans.comp_app,
      Functor.mapIso_hom, Category.assoc]
  have hf : (ordinaryScalarTensorIso φ Y).hom.app (F.obj K) ≫
      (properConstantProjectionIso A p (ordinaryCoefficientComplex φ) K).hom =
      U.map (q.hom.app K) ≫
        (scalarRestrictionDirectImageMap φ p).app ((scalarExtension φ Z).obj K) ≫
        F.map ((ordinaryScalarTensorIso φ Z).hom.app K) := by
    apply (cancel_epi (bY.inv.app (F.obj K))).1
    rw [heY, heZ]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [F.map_comp, reassoc_of% hb]
    exact ht
  apply (cancel_mono
    (properConstantProjectionIso A p (ordinaryCoefficientComplex φ) K).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hf]
  rw [← U.map_comp_assoc, Iso.inv_hom_id_app]
  erw [U.map_id]
  simp only [Category.id_comp]
  have hδ := (asIso (scalarRestrictionDirectImageMap φ p)).inv_hom_id_app
    ((scalarExtension φ Z).obj K)
  simpa only [asIso_inv, asIso_hom, Category.assoc, Category.id_comp] using
    congrArg (fun a ↦ a ≫ F.map ((ordinaryScalarTensorIso φ Z).hom.app K)) hδ


end AlgebraicGeometry.Etale
