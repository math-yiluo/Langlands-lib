/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionReductionUniversal
import all WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel

/-!
# Extension by zero on the small model preserves reduced modules

## References

* Stacks Project Tags 03DA, 03DI and 0E8I
* Stacks Project, Modules on Sites, Tags 03D1 and 03DA
* Stacks Project, Modules on Sites, Tag 03D1
* Stacks Project, Modules on Sites, Tag 03DJ
* Stacks Project, Tags 00VC and 099L
* Stacks Project, Sites, Tag 00XZ
* Stacks Project, Categories, Tag 001J
* Stacks Project, Modules on Sites, Tags 03DA and 03DI
* Stacks Project, Modules on Sites, Tags 03DA and 03DJ
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe t u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]

/-- Pushforward commutes with restriction of scalars along a commutative square of
ring maps; both modules have the same sections. -/
def pushforwardRestrictScalarsIso {S S' : Sheaf J RingCat.{u}} {R R' : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (φ' : S' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    (α : R ⟶ R') (β : S ⟶ S')
    (h : φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map α = β ≫ φ')
    (M : SheafOfModules.{v} R') :
    (pushforward φ).obj ((restrictScalars α).obj M) ≅
      (restrictScalars β).obj ((pushforward φ').obj M) := by
  let L := (forget S).obj ((pushforward φ).obj ((restrictScalars α).obj M))
  let Q := (forget S).obj ((restrictScalars β).obj ((pushforward φ').obj M))
  let g (U : Cᵒᵖ) : L.obj U ≃ₗ[S.obj.obj U] Q.obj U :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        have hh := congrArg (fun t ↦ (t.hom.app U).hom r) h
        exact congrArg (fun q ↦ q • (show M.val.obj (op (F.obj U.unop)) from m)) hh }
  exact (fullyFaithfulForget S).preimageIso (PresheafOfModules.isoMk
    (fun U ↦ (g U).toModuleIso) (fun _ _ _ ↦ by ext; rfl))

end SheafOfModules

namespace AlgebraicGeometry.Scheme

private theorem sfCbcOpenExtension_eq {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    sfCbcOpenExtension j A = cbcRingedOpenExtension (cbcOpenObject j inferInstance)
      (sfCbcConstantSliceIso X (cbcOpenObject j inferInstance) A) := by
  unfold sfCbcOpenExtension cbcRingedOpenExtension sfCbcConstantModuleToSlice
  have hm : sfCbcConstantSliceMap X (cbcOpenObject j inferInstance) A =
      (sfCbcConstantSliceIso X (cbcOpenObject j inferInstance) A).hom := by
    unfold sfCbcConstantSliceMap
    exact (sfCbcConstantSliceMap_existsUnique X _ A).unique
      (sfCbcConstantSliceMap_existsUnique X _ A).exists.choose_spec
      (sfCbcConstantSliceIso_unit X _ A)
  rw [hm]

/-- Transport of modules from an open scheme to the localized ambient site is an equivalence. -/
theorem sfCbcConstantModuleToSlice_isEquivalence (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] : (sfCbcConstantModuleToSlice X W A).IsEquivalence := by
  let := ProEt.sliceDense X W
  let := sfCbcSlice_cocontinuous X W
  have : (ProEt.sliceEquiv X W).functor.IsDenseSubsite
      ((ProEt.topology X).over W) (ProEt.topology W.left) := by
    rw [Equivalence.eq_inducedTopology_of_isDenseSubsite
      ((ProEt.topology X).over W) (ProEt.topology W.left) (ProEt.sliceEquiv X W)]
    infer_instance
  have : (ProEt.sliceEquiv X W).symm.inverse.IsContinuous
      ((ProEt.topology X).over W) (ProEt.topology W.left) :=
    inferInstanceAs ((cbcSliceFunctor X W).IsContinuous
      ((ProEt.topology X).over W) (ProEt.topology W.left))
  have : (ProEt.sliceEquiv X W).symm.functor.IsContinuous
      (ProEt.topology W.left) ((ProEt.topology X).over W) :=
    inferInstanceAs ((ProEt.sliceEquiv X W).inverse.IsContinuous
      (ProEt.topology W.left) ((ProEt.topology X).over W))
  let c := sfCbcConstantSliceIso X W A
  have hm : sfCbcConstantSliceMap X W A = c.hom := by
    unfold sfCbcConstantSliceMap
    exact (sfCbcConstantSliceMap_existsUnique X W A).unique
      (sfCbcConstantSliceMap_existsUnique X W A).exists.choose_spec
      (sfCbcConstantSliceIso_unit X W A)
  have hFE := sfCbcModuleTransport (ProEt.topology W.left)
    ((ProEt.topology X).over W) (ProEt.sliceEquiv X W).symm (adicModuleRing W.left A)
    ((adicModuleRing X A).over W)
    ((sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso c)
  unfold sfCbcConstantModuleToSlice
  rw [hm]
  exact hFE

/-- Restriction to the open scheme, transported to the small models. -/
def sfCbcModelRestriction {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    ConstantCompletion.Mod (sfCbcModelRing X A) ⥤ ConstantCompletion.Mod (sfCbcModelRing U A) :=
  letI := sfCbcConstantModuleToSlice_isEquivalence X (cbcOpenObject j inferInstance) A
  (sfCbcModelModules X A).asEquivalence.inverse ⋙
    SheafOfModules.localizedModuleRestriction (adicConstantRing X A)
      (cbcOpenObject j inferInstance) ⋙
    (sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance) A).asEquivalence.inverse ⋙
    sfCbcModelModules U A

/-- Extension by zero on the small models is left adjoint to restriction. -/
def sfCbcModelExtensionAdjunction {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] : sfCbcModelExtension j A ⊣ sfCbcModelRestriction j A := by
  letI := sfCbcConstantModuleToSlice_isEquivalence X (cbcOpenObject j inferInstance) A
  exact (sfCbcModelModules U A).asEquivalence.symm.toAdjunction.comp
    ((sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance)
      A).asEquivalence.toAdjunction.comp
      ((SheafOfModules.localizedModuleAdjunctionIndependent (adicConstantRing X A)
        (cbcOpenObject j inferInstance)).comp
        (sfCbcModelModules X A).asEquivalence.toAdjunction))


section FiniteCoefficients

variable {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) (n : ℕ)

/-- The finite quotient of the lifted coefficient ring is the lift of the finite quotient. -/
def sfCbcFiniteRingEquiv :
    ULift.{t + 1, t} A ⧸ sfCbcModelIdeal d ^ (n + 1) ≃+* ULift.{t + 1, t} (A ⧸ d.ideal ^ (n + 1)) :=
  (Ideal.quotientEquiv (sfCbcModelIdeal d ^ (n + 1)) (d.ideal ^ (n + 1)) ULift.ringEquiv (by
    rw [Ideal.map_pow, Ideal.map_map]
    have : ((ULift.ringEquiv : ULift.{t + 1, t} A ≃+* A) : ULift.{t + 1, t} A →+* A).comp
        ULift.ringEquiv.symm.toRingHom = RingHom.id A := by
      ext x
      rfl
    rw [this, Ideal.map_id])).trans ULift.ringEquiv.symm

theorem sfCbcFiniteRingEquiv_mk (a : ULift.{t + 1, t} A) :
    sfCbcFiniteRingEquiv d n (Ideal.Quotient.mk _ a) =
      ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down) := rfl

/-- The quotient map of the actual constant coefficient rings on the pro-etale site. -/
abbrev sfCbcFiniteMap (X : Scheme.{t}) :
    adicConstantRing X A ⟶ adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) :=
  adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))

/-- The finite model coefficient sheaf maps isomorphically to the transported finite ring. -/
def sfCbcModelFiniteMap (X : Scheme.{t}) :
    ConstantCompletion.finite (proEtaleModelTopology X) (ULift.{t + 1, t} A)
        (sfCbcModelIdeal d) n ⟶
      ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        CommRingCat.{t + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
          (adicConstantRing X (A ⧸ d.ideal ^ (n + 1))) :=
  (constantSheaf (proEtaleModelTopology X) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (sfCbcFiniteRingEquiv d n).toRingHom) ≫
    sfCbcModelRingMap X (A ⧸ d.ideal ^ (n + 1))

instance (X : Scheme.{t}) : IsIso (sfCbcModelFiniteMap d n X) := by
  have := (sfCbcModelRingMap_existsUnique X (A ⧸ d.ideal ^ (n + 1))).exists.choose_spec.1
  have : IsIso (CommRingCat.ofHom (sfCbcFiniteRingEquiv d n).toRingHom) :=
    (sfCbcFiniteRingEquiv d n).toCommRingCatIso.isIso_hom
  unfold sfCbcModelFiniteMap
  change IsIso (_ ≫ (sfCbcModelRingMap_existsUnique X _).exists.choose)
  infer_instance

/-- The finite model coefficients are compatible with the quotient maps. -/
theorem sfCbcModelFiniteMap_comm (X : Scheme.{t}) :
    ConstantCompletion.quotient (proEtaleModelTopology X) (ULift.{t + 1, t} A)
        (sfCbcModelIdeal d) n ≫ sfCbcModelFiniteMap d n X =
      sfCbcModelRingMap X A ≫
        ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
          CommRingCat.{t + 1} (proEtaleModelTopology X) (ProEt.topology X)).map
            (sfCbcFiniteMap d n X) := by
  let : HasWeakSheafify (proEtaleModelTopology X) CommRingCat.{t + 1} := sfCbcWeakSheafifyModel X
  apply sfCbcSheafifyHomExt (proEtaleModelTopology X)
  intro V
  have hA := (sfCbcModelRingMap_existsUnique X A).exists.choose_spec.2 V.unop
  have hB := (sfCbcModelRingMap_existsUnique X (A ⧸ d.ideal ^ (n + 1))).exists.choose_spec.2
    V.unop
  let J := proEtaleModelTopology X
  let K := ProEt.topology X
  let mk := CommRingCat.ofHom (Ideal.Quotient.mk (sfCbcModelIdeal d ^ (n + 1)))
  let e := CommRingCat.ofHom (sfCbcFiniteRingEquiv d n).toRingHom
  let mkX := CommRingCat.ofHom (RingHom.ulift.{t + 1, t + 1, t, t}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1))))
  have n1 := congrArg (fun f ↦ f.app V)
    (toSheafify_naturality J ((Functor.const (proEtaleSiteModel X)ᵒᵖ).map mk))
  have n2 := congrArg (fun f ↦ f.app V)
    (toSheafify_naturality J ((Functor.const (proEtaleSiteModel X)ᵒᵖ).map e))
  have n3 := congrArg (fun f ↦ f.app (op (AsSmall.down.obj V.unop)))
    (toSheafify_naturality K ((Functor.const X.ProEtᵒᵖ).map mkX))
  simp only [NatTrans.comp_app] at n1 n2 n3
  change (toSheafify J _).app V ≫ (sheafifyMap J _).app V ≫ (sheafifyMap J _).app V ≫
      (sfCbcModelRingMap X (A ⧸ d.ideal ^ (n + 1))).hom.app V =
    (toSheafify J _).app V ≫ (sfCbcModelRingMap X A).hom.app V ≫
      (sheafifyMap K _).app (op (AsSmall.down.obj V.unop))
  rw [← Category.assoc, ← n1, Category.assoc, ← Category.assoc ((toSheafify J _).app V), ← n2,
    Category.assoc]
  erw [hB]
  rw [← Category.assoc ((toSheafify J _).app V)]
  erw [hA, ← n3, ← Category.assoc]

/-- Maps out of the restriction of a constant ring to a slice are determined by their
values on constant sections. -/
theorem sfCbcConstantOver_hom_ext (X : Scheme.{t}) (W : X.ProEt) (B : Type t) [CommRing B]
    {Z : Sheaf ((ProEt.topology X).over W) CommRingCat.{t + 1}}
    (f g : (adicConstantRing X B).over W ⟶ Z)
    (h : ∀ V : Over W,
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} B)))).app
          (op V.left) ≫ f.hom.app (op V) =
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} B)))).app
          (op V.left) ≫ g.hom.app (op V)) : f = g := by
  let : HasWeakSheafify (ProEt.topology X) CommRingCat.{t + 1} := sfCbcWeakSheafifyProEt X
  let : HasWeakSheafify ((ProEt.topology X).over W) CommRingCat.{t + 1} :=
    sfCbcWeakSheafifyOver X W
  let e₀ := ((Over.forget W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} B)))
  apply (cancel_epi e₀.hom).mp
  apply sfCbcSheafifyHomExt ((ProEt.topology X).over W)
  intro V
  have hV := congrArg (fun f ↦ f.app V)
    ((Over.forget W).toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} B))))
  change _ ≫ (e₀.hom.hom.app V ≫ f.hom.app V) = _ ≫ (e₀.hom.hom.app V ≫ g.hom.app V)
  rw [← Category.assoc, ← Category.assoc]
  change _ ≫ e₀.hom.hom.app V = _ at hV
  erw [hV]
  exact h V.unop

/-- The two slice identifications of constant rings are compatible with the quotient maps. -/
private theorem sfCbcConstantSliceIso_square (X : Scheme.{t}) (W : X.ProEt) :
    CbcOpenRingSquare W (sfCbcConstantSliceIso X W A)
      (sfCbcConstantSliceIso X W (A ⧸ d.ideal ^ (n + 1)))
      (sfCbcFiniteMap d n X) (sfCbcFiniteMap d n W.left) := by
  apply sfCbcConstantOver_hom_ext X W A
  intro V
  let mkX := CommRingCat.ofHom (RingHom.ulift.{t + 1, t + 1, t, t}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1))))
  have n1 := congrArg (fun f ↦ f.app (op V.left))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map mkX))
  have n2 := congrArg (fun f ↦ f.app (op ((cbcSliceFunctor X W).obj V)))
    (toSheafify_naturality (ProEt.topology W.left) ((Functor.const W.left.ProEtᵒᵖ).map mkX))
  simp only [NatTrans.comp_app] at n1 n2
  have hA := sfCbcConstantSliceIso_unit X W A V
  have hB := sfCbcConstantSliceIso_unit X W (A ⧸ d.ideal ^ (n + 1)) V
  change _ ≫ (sheafifyMap (ProEt.topology X) _).app (op V.left) ≫
      (sfCbcConstantSliceIso X W (A ⧸ d.ideal ^ (n + 1))).hom.hom.app (op V) =
    _ ≫ (sfCbcConstantSliceIso X W A).hom.hom.app (op V) ≫
      (sheafifyMap (ProEt.topology W.left) _).app (op ((cbcSliceFunctor X W).obj V))
  rw [← Category.assoc, ← n1, Category.assoc]
  erw [hB]
  rw [← Category.assoc]
  erw [hA, ← n2]
  rfl

/-- Transport of finite-coefficient module sheaves to the small model. -/
def sfCbcModelFiniteModules (X : Scheme.{t}) :
    SheafOfModules.{t + 1} (adicModuleRing X (A ⧸ d.ideal ^ (n + 1))) ⥤
      ConstantCompletion.Mod (ConstantCompletion.finite (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) n) :=
  SheafOfModules.pushforward.{t + 1} (F := (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt))
    (J := proEtaleModelTopology X) (K := ProEt.topology X)
    ((sheafCompose (proEtaleModelTopology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (sfCbcModelFiniteMap d n X))

instance (X : Scheme.{t}) : (sfCbcModelFiniteModules d n X).IsEquivalence := by
  let := sfCbcToModel_isEquivalence X (adicModuleRing X (A ⧸ d.ideal ^ (n + 1)))
  let c := (sheafCompose (proEtaleModelTopology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso
      (asIso (sfCbcModelFiniteMap d n X))
  have : (ConstantCompletion.res (sfCbcModelFiniteMap d n X)).IsEquivalence :=
    sfCbcRingIsoRestriction_isEquivalence c
  exact inferInstanceAs (proEtaleModuleToModel (adicModuleRing X (A ⧸ d.ideal ^ (n + 1))) ⋙
    ConstantCompletion.res (sfCbcModelFiniteMap d n X)).IsEquivalence

/-- Model transport commutes with restriction along the finite quotient. -/
def sfCbcModelModulesRestrictIso (X : Scheme.{t})
    (Q : SheafOfModules.{t + 1} (adicModuleRing X (A ⧸ d.ideal ^ (n + 1)))) :
    (sfCbcModelModules X A).obj (reductionRestrict X (sfCbcFiniteMap d n X) |>.obj Q) ≅
      (ConstantCompletion.res (ConstantCompletion.quotient (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) n)).obj
          ((sfCbcModelFiniteModules d n X).obj Q) := by
  have h := congrArg (sheafCompose (proEtaleModelTopology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (sfCbcModelFiniteMap_comm d n X)
  rw [Functor.map_comp, Functor.map_comp] at h
  unfold sfCbcModelModules reductionRestrict
  exact SheafOfModules.pushforwardRestrictScalarsIso _ _ _ _ h.symm Q

private theorem sfCbcConstantSliceMap_eq (X : Scheme.{t}) (W : X.ProEt) (B : Type t)
    [CommRing B] : sfCbcConstantSliceMap X W B = (sfCbcConstantSliceIso X W B).hom := by
  unfold sfCbcConstantSliceMap
  exact (sfCbcConstantSliceMap_existsUnique X W B).unique
    (sfCbcConstantSliceMap_existsUnique X W B).exists.choose_spec
    (sfCbcConstantSliceIso_unit X W B)

end FiniteCoefficients

/-- If equivalences intertwine two functors objectwise, so do their inverses. -/
theorem _root_.CategoryTheory.Functor.nonempty_inverse_obj_iso_of_iso
    {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    (F₁ : C₁ ⥤ D₁) [F₁.IsEquivalence] (F₂ : C₂ ⥤ D₂) [F₂.IsEquivalence]
    (r : C₂ ⥤ C₁) (r' : D₂ ⥤ D₁) (σ : ∀ Q, F₁.obj (r.obj Q) ≅ r'.obj (F₂.obj Q)) (P : D₂) :
    Nonempty (F₁.asEquivalence.inverse.obj (r'.obj P) ≅
      r.obj (F₂.asEquivalence.inverse.obj P)) :=
  ⟨F₁.asEquivalence.inverse.mapIso
      (r'.mapIso (F₂.asEquivalence.counitIso.app P).symm ≪≫ (σ _).symm) ≪≫
    (F₁.asEquivalence.unitIso.app _).symm⟩

/-- Extension by zero on the small models preserves modules reduced at level `n`. -/
theorem sfCbcModelExtension_isReducedModule {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) (n : ℕ)
    (P : ConstantCompletion.Mod (sfCbcModelRing U A))
    (hP : ConstantCompletion.IsReducedModule (proEtaleModelTopology U) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) n P) :
    ConstantCompletion.IsReducedModule (proEtaleModelTopology X) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) n ((sfCbcModelExtension j A).obj P) := by
  obtain ⟨P', ⟨i⟩⟩ := hP
  let W := cbcOpenObject j inferInstance
  obtain ⟨a⟩ := Functor.nonempty_inverse_obj_iso_of_iso (sfCbcModelModules U A)
    (sfCbcModelFiniteModules d n U) (reductionRestrict U (sfCbcFiniteMap d n U))
    (ConstantCompletion.res (ConstantCompletion.quotient (proEtaleModelTopology U)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) n))
    (sfCbcModelModulesRestrictIso d n U) P'
  let Q := (sfCbcModelFiniteModules d n U).asEquivalence.inverse.obj P'
  have hb : Nonempty ((sfCbcOpenExtension j A).obj
      ((reductionRestrict U (sfCbcFiniteMap d n U)).obj Q) ≅
      (reductionRestrict X (sfCbcFiniteMap d n X)).obj
        ((cbcRingedOpenExtension W
          (sfCbcConstantSliceIso X W (A ⧸ d.ideal ^ (n + 1)))).obj Q)) := by
    rw [sfCbcOpenExtension_eq j A]
    exact ⟨(cbcOpenRestrictIso W (sfCbcConstantSliceIso X W A)
      (sfCbcConstantSliceIso X W (A ⧸ d.ideal ^ (n + 1))) (sfCbcFiniteMap d n X)
      (sfCbcFiniteMap d n W.left) (sfCbcConstantSliceIso_square d n X W)).app Q⟩
  obtain ⟨b⟩ := hb
  refine ⟨(sfCbcModelFiniteModules d n X).obj ((cbcRingedOpenExtension W
    (sfCbcConstantSliceIso X W (A ⧸ d.ideal ^ (n + 1)))).obj Q), ⟨?_⟩⟩
  exact (sfCbcModelModulesRestrictIso d n X _).symm ≪≫
    (sfCbcModelModules X A).mapIso (b.symm ≪≫ (sfCbcOpenExtension j A).mapIso a.symm) ≪≫
    (sfCbcModelExtension j A).mapIso i

/-- Restriction on the small models preserves modules reduced at level `n`. -/
theorem sfCbcModelRestriction_isReducedModule {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) (n : ℕ)
    (P : ConstantCompletion.Mod (sfCbcModelRing X A))
    (hP : ConstantCompletion.IsReducedModule (proEtaleModelTopology X) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) n P) :
    ConstantCompletion.IsReducedModule (proEtaleModelTopology U) (ULift.{t + 1, t} A)
      (sfCbcModelIdeal d) n ((sfCbcModelRestriction j A).obj P) := by
  obtain ⟨P', ⟨i⟩⟩ := hP
  let W := cbcOpenObject j inferInstance
  let B := A ⧸ d.ideal ^ (n + 1)
  have := sfCbcConstantModuleToSlice_isEquivalence X W A
  have := sfCbcConstantModuleToSlice_isEquivalence X W B
  have : (cbcSliceFunctor X W).IsContinuous ((ProEt.topology X).over W) (ProEt.topology U) :=
    inferInstanceAs ((cbcSliceFunctor X W).IsContinuous ((ProEt.topology X).over W)
      (ProEt.topology W.left))
  let φX := sfCbcFiniteMap d n X
  let ψ := sfCbcFiniteMap d n U
  let β := ((ProEt.topology X).overPullback RingCat.{t + 1} W).map
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φX)
  obtain ⟨a₁⟩ := Functor.nonempty_inverse_obj_iso_of_iso (sfCbcModelModules X A)
    (sfCbcModelFiniteModules d n X) (reductionRestrict X φX)
    (ConstantCompletion.res (ConstantCompletion.quotient (proEtaleModelTopology X)
      (ULift.{t + 1, t} A) (sfCbcModelIdeal d) n))
    (sfCbcModelModulesRestrictIso d n X) P'
  let Q₁ := (sfCbcModelFiniteModules d n X).asEquivalence.inverse.obj P'
  have a₂ : (SheafOfModules.localizedModuleRestriction (adicConstantRing X A) W).obj
      ((reductionRestrict X φX).obj Q₁) ≅ (SheafOfModules.restrictScalars β).obj
        ((SheafOfModules.localizedModuleRestriction (adicConstantRing X B) W).obj Q₁) := by
    unfold SheafOfModules.localizedModuleRestriction SheafOfModules.overFunctor
      reductionRestrict
    exact SheafOfModules.pushforwardRestrictScalarsIso _ _ _ _ rfl Q₁
  have hσ : ∀ Q₂, (sfCbcConstantModuleToSlice X W A).obj ((reductionRestrict U ψ).obj Q₂) ≅
      (SheafOfModules.restrictScalars β).obj ((sfCbcConstantModuleToSlice X W B).obj Q₂) := by
    intro Q₂
    have h := congrArg (sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (sfCbcConstantSliceIso_square d n X W)
    rw [Functor.map_comp, Functor.map_comp] at h
    unfold sfCbcConstantModuleToSlice reductionRestrict
    rw [sfCbcConstantSliceMap_eq, sfCbcConstantSliceMap_eq]
    exact SheafOfModules.pushforwardRestrictScalarsIso _ _ _ _ h.symm Q₂
  obtain ⟨a₃⟩ := Functor.nonempty_inverse_obj_iso_of_iso (sfCbcConstantModuleToSlice X W A)
    (sfCbcConstantModuleToSlice X W B) (reductionRestrict U ψ)
    (SheafOfModules.restrictScalars β) hσ
    ((SheafOfModules.localizedModuleRestriction (adicConstantRing X B) W).obj Q₁)
  let Q₃ := (sfCbcConstantModuleToSlice X W B).asEquivalence.inverse.obj
    ((SheafOfModules.localizedModuleRestriction (adicConstantRing X B) W).obj Q₁)
  refine ⟨(sfCbcModelFiniteModules d n U).obj Q₃, ⟨?_⟩⟩
  exact (sfCbcModelModulesRestrictIso d n U Q₃).symm ≪≫
    (sfCbcModelModules U A).mapIso (a₃.symm ≪≫
      (sfCbcConstantModuleToSlice X W A).asEquivalence.inverse.mapIso (a₂.symm ≪≫
        (SheafOfModules.localizedModuleRestriction (adicConstantRing X A) W).mapIso a₁.symm)) ≪≫
    (sfCbcModelRestriction j A).mapIso i

end AlgebraicGeometry.Scheme
