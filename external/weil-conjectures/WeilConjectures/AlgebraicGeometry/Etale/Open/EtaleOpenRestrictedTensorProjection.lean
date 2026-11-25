/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.CategoryTheory.SmoothPurity.RestrictedOpenMateTensor
import all WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import all WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSingleCoefficientProjection
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchange
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs

/-! # Restricted scalar change and the open tensor projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory Functor.rightDerivedFunctor
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

private def openCoefficientTensorPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Z : Scheme.{u}} (j : U ⟶ Z) :
    (derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj (scalarCoefficient φ Z) ⋙
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (derivedTensor (ModuleCat.{u + 1} A) U).flip.obj (scalarCoefficient φ U) :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm ≪≫
    derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) j
      (scalarCoefficient φ Z) ≪≫
    Functor.isoWhiskerLeft _
      ((derivedTensor (ModuleCat.{u + 1} A) U).flip.mapIso
        (scalarCoefficientPullbackIso φ j)) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j) _

private theorem openCoefficientTensorPullback_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Z : Scheme.{u}} (j : U ⟶ Z) (L : DerivedCategoryModule A Z) :
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)).hom.app
        ((scalarExtension φ Z).obj L) ≫
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ).map
        ((properOpenCoefficientPullbackIso φ j).hom.app L) ≫
      (scalarTensorIso φ U).hom.app
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) =
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((scalarTensorIso φ Z).hom.app L) ≫
      (openCoefficientTensorPullback φ j).hom.app L := by
  let ε := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
  let T := (derivedTensor (ModuleCat.{u + 1} A) U).flip.obj (scalarCoefficient φ U)
  have h := congrArg (fun z ↦ ε.inv.app
      ((Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).obj
        ((scalarExtension φ Z).obj L)) ≫ z ≫ T.map (ε.hom.app L))
    (scalar_tensor_pullback_square φ j L)
  simp only [scalarRestrictionPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, ε, Iso.inv_hom_id_app_assoc] at h
  have hn := (scalarTensorIso φ U).hom.naturality (ε.hom.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [ε] at hn
  dsimp only [T] at h
  rw [← hn] at h
  have he := ε.inv.naturality ((scalarTensorIso φ Z).hom.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at he
  simp only [ε] at he
  rw [← reassoc_of% he] at h
  simpa only [openCoefficientTensorPullback, properOpenCoefficientPullbackIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, derivedTensorRightCompLeftDerivedUpperStarIso,
    NatIso.ofComponents_hom_app,
    leftDerivedUpperStarTensorIso_hom, Functor.flip_map_app, Functor.flip_obj_map,
    Functor.map_comp, Category.assoc, ε, T] using h

/-- Scalar restriction of the open balancing isomorphism is the inverse open
projection, with the canonical coefficient pullback.
Source: Stacks Tag 0GL6 and the unit normalization of extension by zero
(blueprint: lem-pur-etale-open-restricted-tensor-projection).

Proof: transpose the inverse map under the open adjunction. The unit equations
for scalar open change and open restriction, together with the scalar/tensor
pullback square, identify this transpose with the tensor of the open unit
followed by the inverse pullback/tensor comparison. This is the defining
transpose of the open projection map. Invert the resulting equality. -/
theorem etaleOpenRestrictedTensorProjection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategoryModule A U) :
    (scalarTensorIso φ Z).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((ExceptionalCoefficients.openIso φ j).hom.app K) ≫
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j).inv.app
        ((scalarExtension φ U).obj K) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((scalarTensorIso φ U).hom.app K) =
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) j).inv.app K).app
        (scalarCoefficient φ Z) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        (((derivedTensor (ModuleCat.{u + 1} A) U).obj K).map
          (scalarCoefficientPullbackIso φ j).hom) := by
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  let J' := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory
  let P := (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
  let P' := (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let adj' := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let S := scalarExtension φ U
  let S' := scalarExtension φ Z
  let R := Sheaf.derivedRestrictScalars U.smallEtaleTopology φ
  let R' := Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ
  let T := (derivedTensor (ModuleCat.{u + 1} A) U).flip.obj (scalarCoefficient φ U)
  let T' := (derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj (scalarCoefficient φ Z)
  let p := properOpenCoefficientPullbackIso φ j
  let r : R' ⋙ P ≅ P' ⋙ R :=
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)
  let q := ExceptionalCoefficients.openIso φ j
  let o := derivedRestrictScalarsCompOpenImmersionLowerShriekIso φ j
  let t := openCoefficientTensorPullback φ j
  have hq (L : DerivedCategoryModule A U) :
      S.map (adj.unit.app L) ≫ p.inv.app (J.obj L) =
        adj'.unit.app (S.obj L) ≫ P'.map (q.inv.app L) := by
    simpa only [S, adj, p, J, adj', P', q, SystemProjection.single_open_eq,
      derivedRestriction, derivedExtension] using (scalarOpen_unit φ j L).symm
  have hd : (openDerivedRestrictScalarsIso φ j).symm = r := by
    have he : (openRestrictScalarsIso φ j).symm =
        upperStarRestrictScalarsIsoSheaf φ j :=
      Iso.ext (openRestrictScalarsIso_inv_eq φ j)
    apply Iso.ext
    dsimp only [r]
    simp only [openDerivedRestrictScalarsIso, Functor.mapDerivedCategorySquareIso,
      Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
    rw [← Functor.mapDerivedCategoryNatIso_symm, he]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hr : r.inv = (openDerivedRestrictScalarsIso φ j).hom :=
    congrArg Iso.inv hd.symm
  have ho (L : DerivedCategoryModule B U) :
      R.map (adj'.unit.app L) ≫ r.inv.app (J'.obj L) =
        adj.unit.app (R.obj L) ≫ P.map (o.hom.app L) := by
    have hh := unit_mateEquiv adj' adj (TwoSquare.mk _ _ _ _ o.hom) L
    change _ ≫ (mateEquiv adj' adj (TwoSquare.mk _ _ _ _ o.hom)).app _ = _ at hh
    rw [SystemProjection.single_open_mate, ← hr] at hh
    exact hh
  have h := restricted_left_mate_tensor adj adj' S S' R R' T T'
    (scalarTensorIso φ U) (scalarTensorIso φ Z) p r q o hq ho t
    (openCoefficientTensorPullback_normalization φ j) K
  let l : J.obj (T.obj K) ≅ T'.obj (J.obj K) :=
    J.mapIso ((scalarTensorIso φ U).symm.app K) ≪≫ o.app (S.obj K) ≪≫
      R'.mapIso (q.symm.app K) ≪≫ (scalarTensorIso φ Z).app (J.obj K)
  let d : J.obj (T.obj K) ≅ T'.obj (J.obj K) :=
    J.mapIso (((derivedTensor (ModuleCat.{u + 1} A) U).obj K).mapIso
      (scalarCoefficientPullbackIso φ j).symm) ≪≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) j).app K).app
        (scalarCoefficient φ Z)
  have hp : d.hom =
      (adj.homEquiv _ _).symm (T.map (adj.unit.app K) ≫ t.inv.app (J.obj K)) := by
    apply (adj.homEquiv _ _).injective
    dsimp only [Functor.comp_obj, Functor.id_obj] at *
    rw [Equiv.apply_symm_apply]
    simp only [d, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
    rw [adj.homEquiv_naturality_left]
    change _ ≫ adj.homEquiv _ _
      (((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} A) j).app
        K).app (scalarCoefficient φ Z)) = _
    rw [derivedOpenImmersionLowerShriekProjectionMap, Adjunction.projectionMap_app_app,
      Equiv.apply_symm_apply]
    let E := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
    let TU := derivedTensor (ModuleCat.{u + 1} A) U
    let L := (scalarCoefficientPullbackIso φ j)
    let F := (upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor
    simp only [Adjunction.projectionMapTranspose, NatTrans.comp_app,
      Functor.whiskeringLeft₂_map_app_app_app_app,
      Functor.whiskeringLeft₂_obj_obj_map_app_app, Functor.id_obj]
    simp only [t, openCoefficientTensorPullback, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.mapIso_inv, Category.assoc]
    change (TU.obj K).map L.inv ≫
        (TU.map (adj.unit.app K)).app (F.obj (scalarCoefficient φ Z)) ≫
        (TU.map (E.inv.app (J.obj K))).app (F.obj (scalarCoefficient φ Z)) ≫
        ((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).inv.app
          (J.obj K)).app (scalarCoefficient φ Z) ≫
        E.hom.app _ =
      (TU.map (adj.unit.app K)).app (scalarCoefficient φ U) ≫
        (TU.map (E.inv.app (J.obj K))).app (scalarCoefficient φ U) ≫
        (TU.obj (F.obj (J.obj K))).map L.inv ≫
        ((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).inv.app
          (J.obj K)).app (scalarCoefficient φ Z) ≫ E.hom.app _
    have n₁ := (TU.map (adj.unit.app K)).naturality L.inv
    have n₂ := (TU.map (E.inv.app (J.obj K))).naturality L.inv
    dsimp only [Functor.id_obj] at n₁ n₂
    rw [reassoc_of% n₁, reassoc_of% n₂]
  have he : l.hom = d.hom := h.trans hp.symm
  have hi := congrArg Iso.inv (Iso.ext he)
  simpa only [l, d, Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_inv, Functor.map_comp, J, S, R', q, o, Category.assoc] using hi

end AlgebraicGeometry.Etale
