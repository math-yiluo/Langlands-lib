/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
import all WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Proper direct image preserves a universal finite-coefficient tensor unit

Source: Stacks Project, Tags 0F0G and 0GL6
(blueprint: lem-fix-etale-proper-coefficient-tensor-unit).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem scalar_projection_ambient
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (J : DerivedCategoryModule A Z) :
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).map
        ((scalarMate φ f).app J) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ Z).obj J) =
      (scalarTensorIso φ W).hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) Z).obj J).map
              (scalarCoefficientPullbackIso φ f).hom ≫
            (scalarTensorIso φ Z).inv.app J) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let T := derivedTensor (ModuleCat.{u + 1} A) Z
  let b := (scalarCoefficientPullbackIso φ f).hom
  have ht := (T.map (adj.counit.app J)).naturality b
  dsimp +instances only [Functor.comp_obj, Functor.id_obj] at ht
  have hp : adj.homEquiv _ _
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J)).app
          (scalarCoefficient φ W) ≫
        (T.obj (L(upperStar (ModuleCat.{u + 1} A) f).obj
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J))).map b ≫
        (T.flip.obj (scalarCoefficient φ Z)).map (adj.counit.app J)) =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map ((T.obj J).map b) := by
    simp +instances only [Functor.flip_obj_map, Functor.id_obj]
    rw [ht, ← Category.assoc, adj.homEquiv_naturality_right]
    rfl
  have hm := restricted_mate_tensor adj
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (scalarExtension φ W) (scalarExtension φ Z)
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
    (scalarPullbackIso φ f).hom (scalarRestrictionPullbackIso φ f).hom
    ((derivedTensor (ModuleCat.{u + 1} A) W).flip.obj (scalarCoefficient φ W))
    (T.flip.obj (scalarCoefficient φ Z))
    (scalarTensorIso φ W) (scalarTensorIso φ Z)
    (fun C ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app C).app
        (scalarCoefficient φ W) ≫
      (T.obj (L(upperStar (ModuleCat.{u + 1} A) f).obj C)).map b)
    (scalar_tensor_pullback_square φ f) J
  simp +instances only [Functor.flip_obj_obj, Functor.flip_obj_map, Functor.id_obj,
    Category.assoc] at hp hm
  rw [hp] at hm
  simpa only [scalarMate, scalarRestrictionDirectImageMap, adj, T, b,
    TwoSquare.mk, Functor.map_comp,
    Category.assoc] using hm

private theorem scalar_directImage_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarRestrictionDirectImageMap φ f) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let α := (mateEquiv x z).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)
  have : IsIso α := (ProEtale.scalarPullbackReverse_isIso φ f).2
  have h := iterated_mateEquiv_conjugateEquiv x z a b α
  rw [Equiv.apply_symm_apply] at h
  change scalarRestrictionDirectImageMap φ f = _ at h
  rw [h]
  infer_instance

private theorem proper_scalarMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (J : DerivedCategoryModule A X) : IsIso ((scalarMate φ p).app J) := by
  have := scalar_directImage_isIso φ p
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A p
  have h := scalar_projection_ambient φ p J
  have : IsIso ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      ((scalarMate φ p).app J) ≫
      (scalarRestrictionDirectImageMap φ p).app ((scalarExtension φ X).obj J)) := by
    rw [h]
    infer_instance
  have : IsIso ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
      ((scalarMate φ p).app J))  := IsIso.of_isIso_comp_right _
        ((scalarRestrictionDirectImageMap φ p).app ((scalarExtension φ X).obj J))
  rw [_root_.DerivedCategory.isIso_iff]
  intro q
  have : IsIso ((Sheaf.restrictScalars Y.smallEtaleTopology φ).map
      ((_root_.DerivedCategory.homologyFunctor _ q).map ((scalarMate φ p).app J))) :=
    (NatIso.isIso_map_iff
      ((Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryHomologyFunctorIso q)
      ((scalarMate φ p).app J)).mpr (by
        change IsIso ((_root_.DerivedCategory.homologyFunctor _ q).map
          ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
            ((scalarMate φ p).app J)))
        infer_instance)
  exact isIso_of_reflects_iso _ (Sheaf.restrictScalars Y.smallEtaleTopology φ)

private theorem scalar_unit_directImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A X) :
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj K) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map ((scalarMate φ f).app K) ≫
      (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj K) =
    R(lowerStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app K) := by
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let α := scalarPullbackIso φ f
  have he := iterated_mateEquiv_conjugateEquiv a b x z α.hom
  have hd := iterated_mateEquiv_conjugateEquiv x z a b
    ((mateEquiv x z).symm (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom))
  rw [Equiv.apply_symm_apply] at hd
  have hα : ((mateEquiv x z).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom)) = α.inv := by
    exact congrArg Iso.inv (scalarPullback_eq φ f)
  have hsq : (mateEquiv x z).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom) =
      TwoSquare.mk _ _ _ _ α.inv := hα
  rw [hsq] at hd
  have h := unit_mateEquiv z x
    (mateEquiv a b (TwoSquare.mk _ _ _ _ α.hom)) K
  dsimp +instances only [TwoSquare.mk] at he h
  rw [he] at h
  change R(lowerStar (ModuleCat.{u + 1} A) f).map (z.unit.app K) ≫
      (conjugateIsoEquiv (a.comp z) (x.comp b) α).hom.app
        ((scalarExtension φ X).obj K) =
    x.unit.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj K) ≫
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
        ((scalarMate φ f).app K) at h
  rw [← reassoc_of% h]
  rw [show scalarRestrictionDirectImageMap φ f = _ from hd]
  have hinv : (conjugateEquiv (x.comp b) (a.comp z)
      (TwoSquare.mk _ _ _ _ α.inv)) =
      (conjugateIsoEquiv (a.comp z) (x.comp b) α).inv := rfl
  rw [hinv]
  rw [Iso.hom_inv_id_app]
  dsimp +instances only [scalarExtension, ProEtale.pbcFixedScalarExtension, Functor.comp_obj]
  exact Category.comp_id _

attribute [local irreducible] upperStar

end AlgebraicGeometry.Etale
