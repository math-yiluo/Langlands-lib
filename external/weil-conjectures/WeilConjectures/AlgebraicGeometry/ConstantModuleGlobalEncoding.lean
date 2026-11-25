/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor

/-! # Global fixed-scalar encoding of internal coefficient modules

Source: Stacks Project, Tags 00YV, 03CY and 04IX.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 2000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private noncomputable def smallRegularIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).obj (Mod.regular R) ≅
      SheafOfModules.unit (siteModuleRings (smallRing X R)) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext x
    rfl
  · intro V W f
    rfl

private noncomputable def resRegularIso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ≅ S) :
    (ConstantCompletion.res c.hom).obj (SheafOfModules.unit (siteModuleRings S)) ≅
      SheafOfModules.unit (siteModuleRings R) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let eV := ((sheafToPresheaf J RingCat.{u + 1}).mapIso
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)).app V
    exact ModuleCat.restrictScalarsIsoOfEquiv eV.ringCatIsoToRingEquiv
  · intro V W f
    ext s
    change c.inv.hom.app W (S.obj.map f s) = R.obj.map f (c.inv.hom.app V s)
    exact ConcreteCategory.congr_hom (c.inv.hom.naturality f) s

attribute [local instance] SheafOfModules.monoidalCategory
private noncomputable def fixedRegularIso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] :
    (coefficientModelFixedScalars J k).obj
        (SheafOfModules.unit (siteModuleRings (ConstantCompletion.constant J k))) ≅
      (constantSheaf J (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k) := by
  letI : (ConstantScalarRestriction.restriction J k).Monoidal :=
    (ConstantScalarRestriction.ordinary J k).braided.toMonoidal
  let i : ConstantScalarRestriction.restriction J k ≅ coefficientModelFixedScalars J k := by
    simpa only [ConstantScalarRestriction.restriction, ringRestriction,
      coefficientRingIso, Iso.app_inv]
      using restrictionIso J k
  letI : (coefficientModelFixedScalars J k).Monoidal := Functor.Monoidal.transport i
  exact (Functor.Monoidal.εIso (coefficientModelFixedScalars J k)).symm ≪≫
    ConstantScalarRestriction.fixedUnitIso J k
private noncomputable def modelRegularIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) :
    (coefficientModelFixedScalars _ k).obj
        ((smallModules X R ⋙ ConstantCompletion.res c.hom).obj (Mod.regular R)) ≅
      (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k) :=
  (coefficientModelFixedScalars _ k).mapIso
    ((ConstantCompletion.res c.hom).mapIso (smallRegularIso X R) ≪≫ resRegularIso _ c) ≪≫
      fixedRegularIso _ k

private theorem resEquivalence
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ≅ S) :
    (ConstantCompletion.res c.hom).IsEquivalence := by
  let a := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{u + 1} a.hom)
    (SheafOfModules.restrictScalars.{u + 1} a.inv)
    (ConstantScalarRestriction.restrictCancelIso J a.inv a.hom a.inv_hom_id).symm
    (ConstantScalarRestriction.restrictCancelIso J a.hom a.inv a.hom_inv_id)
  exact e.isEquivalence_functor

private theorem smallEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (smallModules X R).IsEquivalence := by
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) R)
  let B := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)).obj A
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, u} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} X
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).IsContinuous
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (J := Scheme.ProEt.topology X)
    (K := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)
  have : e.inverse.IsEquivalence := e.isEquivalence_inverse
  exact inferInstanceAs
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) R).functor ⋙ e.inverse).IsEquivalence

private noncomputable def sectionEncoding (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) :
    SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) R)) ⥤
        Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} k) :=
  SheafOfModules.pushforward (F := AsSmall.down)
    (J := Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (K := Scheme.ProEt.topology X) (𝟙 _) ⋙
    ConstantCompletion.res c.hom ⋙ coefficientModelFixedScalars _ k

private noncomputable def encoding (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} k) :=
  smallModules X R ⋙ ConstantCompletion.res c.hom ⋙ coefficientModelFixedScalars _ k

@[irreducible] private noncomputable def encodingEquivalence (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ≌
      Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} k) := by
  have := smallEquivalence X R
  have := resEquivalence (Scheme.coefficientProEtaleModelTopology.{u, u} X) c
  have := coefficientModelFixedScalars_isEquivalence
    (Scheme.coefficientProEtaleModelTopology.{u, u} X) k
  have : (encoding X R k c).IsEquivalence :=
    inferInstanceAs (smallModules X R ⋙ ConstantCompletion.res c.hom ⋙
      coefficientModelFixedScalars _ k).IsEquivalence
  exact (encoding X R k c).asEquivalence

private theorem encodingEquivalence_functor (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X R) :
    (encodingEquivalence X R k c).functor = encoding X R k c := by
  unfold encodingEquivalence
  rfl

private noncomputable def sectionDirectEncodingComparison
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
      smallRing Y (condensedRingObj Λ Y))
    (hd : ∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
      ((InternalModuleOperations.coefficientMap Λ f).hom.app
        (AsSmall.down.op.obj V)).hom
          (c.hom.hom.app V
            ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
              ((Functor.const _).obj (CommRingCat.of k))).app V a)) =
        d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)
          ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
            ((Functor.const _).obj (CommRingCat.of k))).app
              ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a)) :
    InternalModuleOperations.lowerStar Λ f ⋙
        sectionEncoding X (condensedRingObj Λ X) k c ≅
      sectionEncoding Y (condensedRingObj Λ Y) k d ⋙
        (Scheme.coefficientProEtaleModelBaseChange.{u, u} f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} k) (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            (Scheme.coefficientProEtaleModelTopology.{u, u} Y) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_)) ?_
  · intro a
    ext x
    symm
    change ((InternalModuleOperations.coefficientMap Λ f).hom.app
      (AsSmall.down.op.obj V)).hom
        (c.hom.hom.app V
          ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            ((Functor.const _).obj (CommRingCat.of k))).app V a)) •
        (show M.val.obj ((InternalModuleOperations.siteMap f).op.obj
          (AsSmall.down.op.obj V)) from x) =
      d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)
        ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
          ((Functor.const _).obj (CommRingCat.of k))).app
            ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a) •
        (show M.val.obj ((InternalModuleOperations.siteMap f).op.obj
          (AsSmall.down.op.obj V)) from x)
    rw [hd V a]
  · intro V W a
    ext x
    rfl
  · intro M N a
    ext V x
    rfl

private theorem encoding_eq_section
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    encoding X (condensedRingObj Λ X) k c =
      (InternalModuleOperations.equivalence Λ X).functor ⋙
        sectionEncoding X (condensedRingObj Λ X) k c := by
  rfl

private noncomputable def directEncodingComparison
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
      smallRing Y (condensedRingObj Λ Y))
    (hd : ∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
      ((InternalModuleOperations.coefficientMap Λ f).hom.app
        (AsSmall.down.op.obj V)).hom
          (c.hom.hom.app V
            ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
              ((Functor.const _).obj (CommRingCat.of k))).app V a)) =
        d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)
          ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
            ((Functor.const _).obj (CommRingCat.of k))).app
              ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a)) :
    CondensedRing.lowerStar Λ f ⋙ encoding X (condensedRingObj Λ X) k c ≅
      encoding Y (condensedRingObj Λ Y) k d ⋙
        (Scheme.coefficientProEtaleModelBaseChange.{u, u} f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} k) (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            (Scheme.coefficientProEtaleModelTopology.{u, u} Y) := by
  rw [encoding_eq_section, encoding_eq_section]
  exact Functor.isoWhiskerRight (InternalModuleOperations.lowerComparison Λ f)
      (sectionEncoding X (condensedRingObj Λ X) k c) ≪≫
    Functor.isoWhiskerLeft (InternalModuleOperations.equivalence Λ Y).functor
      (sectionDirectEncodingComparison f Λ k c d hd)

private noncomputable def pullbackEncodingComparison
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
      smallRing Y (condensedRingObj Λ Y))
    (h : CondensedRing.lowerStar Λ f ⋙ encoding X (condensedRingObj Λ X) k c ≅
      encoding Y (condensedRingObj Λ Y) k d ⋙
        (Scheme.coefficientProEtaleModelBaseChange.{u, u} f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} k) (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            (Scheme.coefficientProEtaleModelTopology.{u, u} Y)) :
    CondensedRing.upperStar Λ f ⋙ encoding Y (condensedRingObj Λ Y) k d ≅
      encoding X (condensedRingObj Λ X) k c ⋙
        Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k := by
  let EX := encodingEquivalence X (condensedRingObj Λ X) k c
  let EY := encodingEquivalence Y (condensedRingObj Λ Y) k d
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, u} f) (ModuleCat.{u + 1} k)
    (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
  let b := EX.toAdjunction.comp (a.comp EY.symm.toAdjunction)
  let P := Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k
  let Q := (Scheme.coefficientProEtaleModelBaseChange.{u, u} f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} k) (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
  let h' : CondensedRing.lowerStar Λ f ⋙ EX.functor ≅ EY.functor ⋙ Q := by
    simpa only [EX, EY, encodingEquivalence_functor] using h
  let r : EY.functor ⋙ Q ⋙ EX.inverse ≅ CondensedRing.lowerStar Λ f :=
    (Functor.associator EY.functor Q EX.inverse).symm ≪≫
      Functor.isoWhiskerRight h'.symm EX.inverse ≪≫
      Functor.associator (CondensedRing.lowerStar Λ f) EX.functor EX.inverse ≪≫
      Functor.isoWhiskerLeft (CondensedRing.lowerStar Λ f) EX.unitIso.symm ≪≫
      (CondensedRing.lowerStar Λ f).rightUnitor
  let t := (CondensedRing.upperStarLowerStarAdjunction Λ f).leftAdjointUniq
    (b.ofNatIsoRight r)
  simpa only [EX, EY, encodingEquivalence_functor] using
    (Functor.isoWhiskerRight t EY.functor ≪≫
    Functor.associator EX.functor (P ⋙ EY.inverse) EY.functor ≪≫
    Functor.isoWhiskerLeft EX.functor (Functor.associator P EY.inverse EY.functor ≪≫
      Functor.isoWhiskerLeft P EY.counitIso ≪≫ P.rightUnitor))

/-- Global encoding, its regular module, and its coordinate-normalized inverse-image comparison.

Source: Stacks Project, Tags 00YV, 03CY and 03D2.
(auxiliary; not a blueprint node).

Proof: compose sectionModuleEquivalence, AsSmall transport, restriction along c,
and the constant-ring/fixed-scalar equivalence. The regular module is sent to the
unit by the section construction, the scalar ring isomorphism and the monoidal
fixed-scalar equivalence. For inverse image, compare right adjoints on sections:
the identity additive map is k-linear by the given equation on constant sections.
Conjugate the two specified adjunctions and apply uniqueness of left adjoints.
The constructions are explicit; no coordinate or equivalence is chosen from a
mere unproved existence statement. -/
theorem constant_module_global_encoding
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    ∃ E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ≌
        Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) (ModuleCat.{u + 1} k),
      E.functor = smallModules X (condensedRingObj Λ X) ⋙ ConstantCompletion.res c.hom ⋙
        coefficientModelFixedScalars _ k ∧
      Nonempty (E.functor.obj (Mod.regular (condensedRingObj Λ X)) ≅
        (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k)) ∧
      ∀ {Y : Scheme.{u}} (f : Y ⟶ X)
        (d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
          smallRing Y (condensedRingObj Λ Y)),
        (∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
          ((InternalModuleOperations.coefficientMap Λ f).hom.app
            (AsSmall.down.op.obj V)).hom
              (c.hom.hom.app V
                ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
                  ((Functor.const _).obj (CommRingCat.of k))).app V a)) =
            d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)
              ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
                ((Functor.const _).obj (CommRingCat.of k))).app
                  ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a)) →
        Nonempty (CondensedRing.upperStar Λ f ⋙
          (smallModules Y (condensedRingObj Λ Y) ⋙ ConstantCompletion.res d.hom ⋙
            coefficientModelFixedScalars _ k) ≅
          E.functor ⋙ Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k) := by
  let E := encodingEquivalence X (condensedRingObj Λ X) k c
  have hE : E.functor = encoding X (condensedRingObj Λ X) k c :=
    encodingEquivalence_functor X (condensedRingObj Λ X) k c
  refine ⟨E, hE, ?_, ?_⟩
  · exact ⟨(eqToIso (congrArg (fun F ↦ F.obj (Mod.regular (condensedRingObj Λ X))) hE)) ≪≫
      modelRegularIso X (condensedRingObj Λ X) k c⟩
  · intro Y f d hd
    exact ⟨pullbackEncodingComparison f Λ k c d (directEncodingComparison f Λ k c d hd) ≪≫
      Functor.isoWhiskerRight (eqToIso hE).symm
        (Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k)⟩

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
