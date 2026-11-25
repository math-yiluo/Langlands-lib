/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingNaturality
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding

/-! # Normalized finite coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem encoding_smul (T : Scheme.{u}) (e : Encoding A T)
    (M : Internal A T) (V : T.ProEtᵒᵖ) (a : ULift.{u + 1} A)
    (m : M.X.obj.obj V) :
    (show M.X.obj.obj V from a •
      (show ((sectionEncoding A T e.ringIso ⋙ fixedRestriction A T).obj M).obj.obj V from m)) =
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (coefficient A) T) M.X).app V ≫
        (Mod.act (A := condensedRingObj (coefficient A) T) M.X).hom.app V).hom
        ((((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (canonicalAbelianMap A T).hom).app V).hom a) ⊗ₜ[ℤ] m) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let c := (constantCommuteCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app (CommRingCat.of B)
  have hc : Scheme.proEtaleModuleScalarUnit T A ≫ c.hom.hom =
      toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B)) := by
    change _ ≫ ((constantCommuteCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of B)).hom = _
    erw [constantCommuteCompose_hom_app_hom]
    unfold Scheme.proEtaleModuleScalarUnit
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of B)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  have hi : toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B)) ≫ c.inv.hom =
      Scheme.proEtaleModuleScalarUnit T A := by
    rw [← hc, Category.assoc]
    change _ ≫ (c.hom ≫ c.inv).hom = _
    rw [Iso.hom_inv_id]
    exact Category.comp_id _
  change ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
      (condensedRingObj (coefficient A) T) M.X).app V ≫
      (Mod.act (A := condensedRingObj (coefficient A) T) M.X).hom.app V).hom
    (e.ringIso.hom.hom.app V (c.inv.hom.app V
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B))).app V a)) ⊗ₜ[ℤ] m) = _
  erw [ConcreteCategory.congr_hom (congr_app hi V) a]
  apply congrArg (fun r ↦ ((Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{u + 1})
    (condensedRingObj (coefficient A) T) M.X).app V ≫
      (Mod.act (A := condensedRingObj (coefficient A) T) M.X).hom.app V).hom
        (r ⊗ₜ[ℤ] m))
  exact e.normalization V a

private theorem pushforward_action
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T U : Scheme.{u}) (f : U ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (V : T.ProEtᵒᵖ) (r : (condensedRingObj Λ T).obj.obj V)
    (m : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)) :
    (show M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) from
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T) ((CondensedRing.lowerStar Λ f).obj M).X).app V ≫
      (Mod.act ((CondensedRing.lowerStar Λ f).obj M).X).hom.app V).hom (r ⊗ₜ[ℤ] m)) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ U) M.X).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) ≫
      (Mod.act M.X).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)).hom
        (((condensedPushforwardHom Λ f).hom.app V).hom r ⊗ₜ[ℤ] m) := by
  have := Scheme.ProEt.isContinuous_overPullback f
  exact InternalModuleOperations.section_action (Scheme.ProEt.topology T)
    (Scheme.ProEt.topology U) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
    (condensedRingObj Λ U) (condensedRingObj Λ T) M.X
    (condensedPushforwardHom Λ f) (Mod.act M.X) V r m

private theorem encodedPushforward_action (T U : Scheme.{u}) (f : U ⟶ T)
    (e : Encoding A T) (M : Internal A U) (V : T.ProEtᵒᵖ) (a : ULift.{u + 1} A)
    (m : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)) :
    (show M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) from
      (ModuleCat.smul (((sectionEncoding A T e.ringIso ⋙ fixedRestriction A T).obj
        ((CondensedRing.lowerStar (coefficient A) f).obj M)).obj.obj V) a).asHom.hom m) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (coefficient A) T)
        ((CondensedRing.lowerStar (coefficient A) f).obj M).X).app V ≫
      (Mod.act ((CondensedRing.lowerStar (coefficient A) f).obj M).X).hom.app V).hom
        ((((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (canonicalAbelianMap A T).hom).app V).hom a) ⊗ₜ[ℤ] m) := by
  exact encoding_smul A T e ((CondensedRing.lowerStar (coefficient A) f).obj M) V a m

private theorem fixedPushforward_action (T U : Scheme.{u}) (f : U ⟶ T)
    (e : Encoding A U) (M : Internal A U) (V : T.ProEtᵒᵖ) (a : ULift.{u + 1} A)
    (m : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)) :
    (show M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) from
      (ModuleCat.smul (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
        ((sectionEncoding A U e.ringIso ⋙ fixedRestriction A U).obj M)).obj.obj V) a).asHom.hom m) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (coefficient A) U) M.X).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) ≫
      (Mod.act M.X).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)).hom
        (((toSheafify (Scheme.ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (canonicalAbelianMap A U).hom).app
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) a) ⊗ₜ[ℤ] m) := by
  exact encoding_smul A U e M _ a m

private theorem abelian_comp_eq_apply {B C D : Ab.{u + 1}}
    (g : B ⟶ C) (h : C ⟶ D) (k : B ⟶ D) (he : g ≫ h = k) (x : B) :
    h.hom (g.hom x) = k.hom x := by
  exact congrArg (fun z : B ⟶ D ↦ z.hom x) he

private theorem canonicalPushforward_apply (T U : Scheme.{u}) (f : U ⟶ T)
    (V : T.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    ((condensedPushforwardHom (coefficient A) f).hom.app V).hom
      (((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
          (canonicalAbelianMap A T).hom).app V).hom a) =
    ((toSheafify (Scheme.ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
        (canonicalAbelianMap A U).hom).app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)).hom a := by
  exact abelian_comp_eq_apply _ _ _ (canonicalAbelianMap_naturality A T U f V) a

private theorem normalizedPushforward_action (T U : Scheme.{u}) (f : U ⟶ T)
    (M : Internal A U) (V : T.ProEtᵒᵖ) (a : ULift.{u + 1} A)
    (m : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)) :
    (show M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) from
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (coefficient A) T)
        ((CondensedRing.lowerStar (coefficient A) f).obj M).X).app V ≫
      (Mod.act ((CondensedRing.lowerStar (coefficient A) f).obj M).X).hom.app V).hom
        ((((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (canonicalAbelianMap A T).hom).app V).hom a) ⊗ₜ[ℤ] m)) =
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (coefficient A) U) M.X).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) ≫
      (Mod.act M.X).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)).hom
        (((toSheafify (Scheme.ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
            (canonicalAbelianMap A U).hom).app
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) a) ⊗ₜ[ℤ] m) := by
  refine (pushforward_action (coefficient A) T U f M V _ m).trans ?_
  exact congrArg (fun r ↦ ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (coefficient A) U) M.X).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) ≫
      (Mod.act M.X).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)).hom
          (r ⊗ₜ[ℤ] m)) (canonicalPushforward_apply A T U f V a)

attribute [local irreducible] canonicalAbelianMap

/-- The common underlying direct-image sections have the same constant scalar action.
Source: normalized constant-section action and coefficient naturality
(auxiliary; not a blueprint node). -/
theorem sectionPushforward_smul (T U : Scheme.{u}) (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) (M : Internal A U)
    (V : T.ProEtᵒᵖ) (a : ULift.{u + 1} A)
    (m : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)) :
    (show M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) from
      (ModuleCat.smul (((sectionEncoding A T eT.ringIso ⋙ fixedRestriction A T).obj
      ((CondensedRing.lowerStar (coefficient A) f).obj M)).obj.obj V) a).asHom.hom m) =
    (show M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V) from
      (ModuleCat.smul (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
        ((sectionEncoding A U eU.ringIso ⋙ fixedRestriction A U).obj M)).obj.obj V)
        a).asHom.hom m) := by
  exact (encodedPushforward_action A T U f eT M V a m).trans
    ((normalizedPushforward_action A T U f M V a m).trans
      (fixedPushforward_action A T U f eU M V a m).symm)

/-- The identity on additive direct-image sections, as an isomorphism of module sheaves.
Source: normalized constant-section action and coefficient naturality
(auxiliary; not a blueprint node). -/
def sectionPushforwardIso (T U : Scheme.{u}) (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) (M : Internal A U) :
    (sectionEncoding A T eT.ringIso ⋙ fixedRestriction A T).obj
      ((CondensedRing.lowerStar (coefficient A) f).obj M) ≅
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
      ((sectionEncoding A U eU.ringIso ⋙ fixedRestriction A U).obj M) := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦ ?_) ?_)
  · refine (show (((sectionEncoding A T eT.ringIso ⋙ fixedRestriction A T).obj
        ((CondensedRing.lowerStar (coefficient A) f).obj M)).obj.obj V : Type (u + 1)) ≃ₗ[
          ULift.{u + 1} A]
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
          ((sectionEncoding A U eU.ringIso ⋙ fixedRestriction A U).obj M)).obj.obj V) from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := sectionPushforward_smul A T U f eT eU M V }).toModuleIso
  · intro V V' g
    ext m
    rfl

/-- The normalized encoding comparison for the complete direct-image functors.
Source: normalized constant-section action and coefficient naturality
(auxiliary; not a blueprint node). -/
def encodingPushforwardNatIso (T U : Scheme.{u}) (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.lowerStar (coefficient A) f ⋙ eT.ordinary.functor ⋙ eT.fixed.functor ≅
      (eU.ordinary.functor ⋙ eU.fixed.functor) ⋙
        lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  rw [eT.ordinary_functor, eT.fixed_functor, eU.ordinary_functor, eU.fixed_functor]
  exact NatIso.ofComponents (sectionPushforwardIso A T U f eT eU) (by
    intro M N g
    ext V m
    dsimp [sectionPushforwardIso, CondensedRing.lowerStar]
    rfl)

/-- Normalized finite-discrete encoding commutes with inverse image.
Source: Stacks Tags 03D6 and 03D7.
(auxiliary; not a blueprint node).

Proof: normalization identifies the scalar action with the internal action of canonical
constant sections. Those sections commute with direct image, so the identity on sections
is a linear natural isomorphism between the two encoded direct images. Conjugate this
isomorphism by the encoding equivalences and use uniqueness of left adjoints. -/
theorem encoding_pullback_fixed [Finite A] [DiscreteTopology A]
    {T U : Scheme.{u}} (f : U ⟶ T) (eT : Encoding A T) (eU : Encoding A U)
    (M : Internal A T) :
    Nonempty ((eU.ordinary.functor ⋙ eU.fixed.functor).obj
        ((CondensedRing.upperStar (coefficient A) f).obj M) ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
        ((eT.ordinary.functor ⋙ eT.fixed.functor).obj M)) := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅ EU.functor ⋙ R :=
    encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact ⟨((a.leftAdjointUniq (b.ofNatIsoRight kr)).app M).symm⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
