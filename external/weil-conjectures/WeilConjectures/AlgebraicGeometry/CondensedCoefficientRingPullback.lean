/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison

/-! # The cartesian section-ring coefficient map

Source: Stacks Project, Tags 00YV and 03D2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 2000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- The actual coefficient map, reconstructed as commutative rings on the small sites.
Source: Stacks Tag 00YV; the underlying additive map is eta_f.
(auxiliary; not a blueprint node). -/
def condensedSmallRingMap
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    smallRing X (condensedRingObj Λ X) ⟶
      ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).obj
        (smallRing Y (condensedRingObj Λ Y)) where
  hom :=
    { app := fun V ↦ @CommRingCat.ofHom _ _
        ((smallRing X (condensedRingObj Λ X)).obj.obj V).commRing
        ((smallRing Y (condensedRingObj Λ Y)).obj.obj
          ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)).commRing
        ((InternalModuleOperations.coefficientMap Λ f).hom.app
          (AsSmall.down.op.obj V)).hom
      naturality := by
        intro V W a
        ext r
        exact ConcreteCategory.congr_hom
          ((InternalModuleOperations.coefficientMap Λ f).hom.naturality
            (AsSmall.down.op.map a)) r }

private theorem originalRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u + 1} X

attribute [local instance] originalRingSheafify

private abbrev smallRingSheafEquivalence (X : Scheme.{u}) :
    Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) CommRingCat.{u + 1} ≌
      Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} := by
  letI := Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  exact CategoryTheory.Equivalence.mk
    ((AsSmall.up :
      X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} X).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Scheme.ProEt.topology X)
          (Scheme.coefficientProEtaleModelTopology.{u, u} X))
    ((AsSmall.down :
      Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (Scheme.ProEt.topology X))
    (Iso.refl _) (Iso.refl _)

@[irreducible] private def smallRingAdjunction {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (smallRingSheafEquivalence X).functor ⋙
      Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
        (smallRingSheafEquivalence Y).inverse ⊣
      (Scheme.coefficientProEtaleModelBaseChange.{u, u} f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (Scheme.coefficientProEtaleModelTopology.{u, u} Y) :=
  (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).restrictFullyFaithful
    (smallRingSheafEquivalence X).fullyFaithfulFunctor
    (smallRingSheafEquivalence Y).fullyFaithfulFunctor (Iso.refl _) (Iso.refl _)

private theorem smallRingAdjunction_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (smallRingAdjunction f).unit.app ((smallRingSheafEquivalence X).inverse.obj R) =
      ⟨Functor.whiskerLeft AsSmall.down.op
        ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom⟩ := by
  apply (smallRingSheafEquivalence X).functor.map_injective
  rw [smallRingAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl

/-- The ring-sheaf adjunct of the actual condensed coefficient map is invertible.

Source: Stacks Project, Sites Tag 00YV and Modules on Sites Tag 03D2;
ring-coordinate transport in step 1 of lem-sfb-constant-slice-module-encoding.
(blueprint: lem-sfb-condensed-coefficient-ring-pullback).

Proof: forget the ring inverse image to underlying abelian sheaves. The canonical
forgetful comparison is an isomorphism: inverse image on sets preserves finite
limits, filtered colimits compute its local sections, and ring/abelian structures
are transported by the same finite operations. The comparison respects the
adjunction units. The sectionRingSheaf reconstruction has exactly the original
underlying abelian sheaf, and condensedSmallRingMap is eta_f on those sections,
by coefficientMap_existsUnique. Consequently its adjunct, after the forgetful
comparison and AsSmall transport, is alpha_f = condensedPullbackHom Λ f.
This is an isomorphism by upperStarFromPointComp. The forgetful functor from
commutative-ring sheaves reflects isomorphisms, so the displayed ring adjunct
is invertible. No coefficient ring k, coordinate c, module, or slice enters this
assertion. The argument also applies to the empty scheme and zero ring. -/
theorem condensedSmallRingMap_pullback_isIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).homEquiv _ _).symm
        (condensedSmallRingMap f Λ)) := by
  obtain ⟨c, hc, _⟩ := spCoefficientIso_existsUnique f Λ
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  let A := smallRing X (condensedRingObj Λ X)
  let B := smallRing Y (condensedRingObj Λ Y)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) CommRingCat.{u + 1}
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
  let e := adj.leftAdjointUniq (smallRingAdjunction f)
  let d : (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).obj A ≅ B :=
    e.app A ≪≫ (smallRingSheafEquivalence Y).inverse.mapIso c
  have hd : adj.homEquiv _ _ d.hom = condensedSmallRingMap f Λ := by
    rw [Adjunction.homEquiv_unit]
    change adj.unit.app A ≫ _ = _
    dsimp only [d, Iso.trans_hom, Iso.app_hom]
    rw [Functor.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
    change (smallRingAdjunction f).unit.app
      ((smallRingSheafEquivalence X).inverse.obj R) ≫ _ = _
    rw [smallRingAdjunction_unit f R]
    ext V r
    change (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
      c.hom).hom.app (AsSmall.down.op.obj V) r =
        ((InternalModuleOperations.coefficientMap Λ f).hom.app
          (AsSmall.down.op.obj V)).hom r
    rw [hc]
    exact ((InternalModuleOperations.coefficientMap_existsUnique Λ f).exists.choose_spec
      (AsSmall.down.op.obj V) r).symm
  change IsIso ((adj.homEquiv A B).symm (condensedSmallRingMap f Λ))
  rw [← hd, Equiv.symm_apply_apply]
  infer_instance

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
