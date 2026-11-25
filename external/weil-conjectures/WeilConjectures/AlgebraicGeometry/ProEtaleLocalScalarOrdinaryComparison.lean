/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.AlgebraicGeometry.ConstantDerivedNormalizationUniversal
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

/-! # Ordinary scalar extension on a pro-etale slice

Source: Stacks Project, Modules on Sites, Tags 03D2, 03EL and 03EK;
Cohomology on Sites, lemma-pullback-tensor-product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.LocalScalar

open SheafOfModules.CoefficientOrdinaryProof
open scoped ChangeOfRings

/-- Read modules using a specified constant scalar action. -/
def fixed {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (S : Sheaf J RingCat.{u + 1}) (B : Type (u + 1)) [CommRing B]
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ S.obj) :
    SheafOfModules.{u + 1} S ⥤ Sheaf J (ModuleCat.{u + 1} B) where
  obj M :=
    { obj :=
        { obj := fun V ↦ ((PresheafOfModules.restrictScalars a).obj M.val).obj V
          map := fun f ↦ ((PresheafOfModules.restrictScalars a).obj M.val).map f
          map_id := fun _ ↦ by ext x; simp; rfl
          map_comp := fun _ _ ↦ by ext x; simp; rfl }
      property := Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun V ↦ (ModuleCat.restrictScalars (a.app V).hom).map (f.val.app V)
      naturality := fun {_ _} g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }

instance fixed_additive {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u + 1})
    (B : Type (u + 1)) [CommRing B]
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ S.obj) : (fixed J S B a).Additive where
  map_add := by intros; ext V x; rfl

/-- Restriction to fixed scalars is exact because it retains the underlying abelian sheaf. -/
theorem fixed_exact {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u + 1})
    (B : Type (u + 1)) [CommRing B]
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ S.obj) :
    PreservesFiniteLimits (fixed J S B a) ∧ PreservesFiniteColimits (fixed J S B a) := by
  let F := fixed J S B a
  let T := sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits T := by
    have : PreservesFiniteLimits (T ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have hleft : (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom B)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom B)).isLeftAdjoint
    exact inferInstanceAs (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom B) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have : PreservesFiniteColimits T := by
    let adj := Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
    have : PreservesLimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).rightAdjoint :=
      adj.rightAdjoint_preservesLimits
    have : J.HasSheafCompose
        (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).rightAdjoint :=
      hasSheafCompose_of_preservesLimitsOfSize _
    have : T.IsLeftAdjoint := (sheafComposeAdjunction J adj).isLeftAdjoint
    infer_instance
  have : ReflectsFiniteLimits T :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteLimits (F ⋙ T) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S))
  have : PreservesFiniteColimits (F ⋙ T) :=
    (moduleSheaves_colimits_forgetful.{u + 1, u, u + 1} S).2.2.1
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F T,
    preservesFiniteColimits_of_reflects_of_preserves F T⟩

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
  CochainComplex.IsKFlatTensor SheafOfModules.monoidalCategory

section GeneralChange

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  {S T : Sheaf J CommRingCat.{u + 1}} (f : S ⟶ T)
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J S))]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J T))]

/-- Scalar extension with its determining ordinary equations and derived universal property. -/
structure ChangeData where
  ordinary : (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J S)) ⥤ (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J T))
  obj_eq : ∀ M, ordinary.obj M =
    SheafOfModules.changeOfRings.{u, u + 1, u + 1} f M
  map_eq : ∀ {M N} (a : M ⟶ N), ordinary.map a = eqToHom (obj_eq M) ≫
    SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} f M a ≫ eqToHom (obj_eq N).symm
  additive : ordinary.Additive
  derived : DerivedCategory (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J S)) ⥤ DerivedCategory (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J T))
  counit :
    letI := additive
    DerivedCategory.Qh ⋙ derived ⟶
      ordinary.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  leftDerived :
    letI := additive
    derived.IsLeftDerivedFunctor counit (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J S)) (.up ℤ))
  kflat_iso :
    letI := additive
    ∀ P : CochainComplex (SheafOfModules.{u + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        J S)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := S) P →
      IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The universal-property theorem determines the packaged derived scalar extension. -/
def extensionData : ChangeData f :=
  let h := SheafOfModules.derivedChangeOfRingsIndependentCoefficients f
  let hd := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2
  { ordinary := h.choose
    obj_eq := h.choose_spec.choose
    map_eq := h.choose_spec.choose_spec.choose
    additive := h.choose_spec.choose_spec.choose_spec.choose
    derived := hd.choose
    counit := hd.choose_spec.choose
    leftDerived := hd.choose_spec.choose_spec.1
    kflat_iso := hd.choose_spec.choose_spec.2.2 }

end GeneralChange

attribute [local irreducible] extensionData

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (B : Type (u + 1)) [CommRing B] (φ : R ⟶ adicLisseConstantRing X B) (U : Y.ProEt)

attribute [local irreducible] proEtaleModuleInverseImage HasDerivedCategory.standard
  completedAdicChangeData Functor.leftAdjoint

/-- Actual inverse image followed by slice restriction. -/
abbrev restriction := proEtaleModuleInverseImage i R ⋙
  ProEtaleLocalRestriction.restriction i R U

/-- Additivity of the exact actual-ring local restriction. -/
instance restriction_additive : (restriction i R U).Additive := by
  let := ProEtaleLocalRestriction.inverseImage_additive i R
  let := ProEtaleLocalRestriction.restriction_additive i R U
  infer_instance

/-- Exactness of the actual-ring local restriction. -/
theorem restriction_exact : PreservesFiniteLimits (restriction i R U) ∧
    PreservesFiniteColimits (restriction i R U) :=
  ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

/-- The scalar map on the slice, with its canonical constant-section normalization. -/
def coefficient :
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U ⟶
      (adicLisseConstantRing Y B).over U :=
  ((ProEt.topology Y).overPullback CommRingCat.{u + 1} U).map
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ ≫
      proEtaleConstantInverseImageMap i CommRingCat.{u + 1} (CommRingCat.of B))

/-- Fixed scalar restriction on the slice uses the original constant section b. -/
abbrev sliceFixed := fixed ((ProEt.topology Y).over U) ((adicLisseRing Y B).over U) B
  (Functor.whiskerLeft (Over.forget U).op (adicLisseConstantUnit Y B))

/-- Source modules on the actual localized inverse-image ring. -/
abbrev source := SheafOfModules.{u + 1}
  ((ProEtaleLocalRestriction.inverseRing i R).over U)

/-- Target modules on the restricted constant ring. -/
abbrev target := SheafOfModules.{u + 1} ((adicLisseRing Y B).over U)

/-- The canonical localization for the source module category. -/
abbrev sourceDerived : HasDerivedCategory.{u + 2} (source i R U) :=
  HasDerivedCategory.standard (source i R U)

/-- The canonical localization for the target module category. -/
abbrev targetDerived : HasDerivedCategory.{u + 2} (target B U) :=
  HasDerivedCategory.standard (target B U)

/-- The same source localization expressed after forgetting commutativity. -/
abbrev sourceExtensionDerived : HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      ((ProEt.topology Y).over U)
      (((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U))) :=
  sourceDerived i R U

/-- The same target localization expressed after forgetting commutativity. -/
abbrev targetExtensionDerived : HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      ((ProEt.topology Y).over U)
      ((adicLisseConstantRing Y B).over U))) := targetDerived B U

/-- Package the already constructed universal extension on the localized ring. -/
def changeData :=
  let R' := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U
  let S' := (adicLisseConstantRing Y B).over U
  letI : HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose ((ProEt.topology Y).over U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')) := sourceDerived i R U
  letI : HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose ((ProEt.topology Y).over U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S')) := targetDerived B U
  extensionData (coefficient i R B φ U)

attribute [local irreducible] changeData

/-- Ordinary sheaf tensor extension on the slice. -/
def change :=
  letI := sourceExtensionDerived i R U
  letI := targetExtensionDerived B U
  (changeData i R B φ U).ordinary

instance change_additive : (change i R B φ U).Additive :=
  letI := sourceExtensionDerived i R U
  letI := targetExtensionDerived B U
  (changeData i R B φ U).additive

/-- Its universal total left derived functor. -/
def derivedChange :=
  letI := sourceExtensionDerived i R U
  letI := targetExtensionDerived B U
  (changeData i R B φ U).derived

/-- Transport a homotopy counit to cochain complexes by the quotient comparisons. -/
def complexCounit {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv LF ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) eps ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).hom

/-- The cochain counit is invertible wherever its homotopy counit is invertible. -/
theorem complexCounit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (eps : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ)
    (h : IsIso (eps.app ((HomotopyCategory.quotient C (.up ℤ)).obj P))) :
    IsIso ((complexCounit F LF eps).app P) := by
  let := h
  dsimp only [complexCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

attribute [local irreducible] complexCounit

/-- The specified homotopy counit of local scalar extension. -/
def derivedCounit :=
  letI := sourceExtensionDerived i R U
  letI := targetExtensionDerived B U
  (changeData i R B φ U).counit

/-- Its cochain counit, in the canonical slice module categories. -/
def counit :=
  letI := sourceDerived i R U
  letI := targetDerived B U
  letI := sourceExtensionDerived i R U
  letI := targetExtensionDerived B U
  letI : (change i R B φ U).Additive := change_additive i R B φ U
  complexCounit
    (C := SheafOfModules.{u + 1} ((ProEtaleLocalRestriction.inverseRing i R).over U))
    (D := SheafOfModules.{u + 1} ((adicLisseRing Y B).over U))
    (change i R B φ U) (derivedChange i R B φ U) (derivedCounit i R B φ U)

/-- The specified local cochain counit computes extension on every K-flat complex. -/
theorem counit_isIso
    (P : CochainComplex (SheafOfModules.{u + 1}
      ((ProEtaleLocalRestriction.inverseRing i R).over U)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients
      (R := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R).over U) P) :
    IsIso ((counit i R B φ U).app P) := by
  let := sourceDerived i R U
  let := targetDerived B U
  let := sourceExtensionDerived i R U
  let := targetExtensionDerived B U
  let : (change i R B φ U).Additive := change_additive i R B φ U
  exact complexCounit_isIso
    (C := SheafOfModules.{u + 1} ((ProEtaleLocalRestriction.inverseRing i R).over U))
    (D := SheafOfModules.{u + 1} ((adicLisseRing Y B).over U))
    (change i R B φ U) (derivedChange i R B φ U) (derivedCounit i R B φ U) P
    ((changeData i R B φ U).kflat_iso P hp)

private def fixedRestrictionIso (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    sfbFixedScalarRestriction X B ≅
      ConstantNormalizationComparison.restriction (ProEt.topology X) B := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun V ↦ ?_) ?_
    · refine
        { hom := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} B)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intros
                exact (ConstantNormalizationComparison.restriction_smul
                  (ProEt.topology X) B M V _ _).symm }
          inv := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} B)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intros
                exact ConstantNormalizationComparison.restriction_smul
                  (ProEt.topology X) B M V _ _ }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
    · intros; ext x; rfl
  · intros; ext V x; rfl

private def fixedEquivalence (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    proEtaleRingModules X (adicLisseConstantRing X B) ≌
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B) := by
  letI : (sfbFixedScalarRestriction X B).IsEquivalence :=
    Functor.isEquivalence_of_iso (fixedRestrictionIso X B).symm
  exact (sfbFixedScalarRestriction X B).asEquivalence

private def globalCoefficient :=
  (proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ ≫
    proEtaleConstantInverseImageMap i CommRingCat.{u + 1} (CommRingCat.of B)

private def constantDirect :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
    (J := ProEt.topology X) (K := ProEt.topology Y)
    (S := adicLisseRing X B) (R := adicLisseRing Y B)
    ⟨Functor.whiskerRight
      (proEtaleConstantDirectImageMap i CommRingCat.{u + 1} (CommRingCat.of B)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private theorem constantDirect_section (V : X.ProEtᵒᵖ) (b : B) :
    (proEtaleConstantDirectImageMap i CommRingCat.{u + 1}
      (CommRingCat.of B)).hom.app V ((adicLisseConstantUnit X B).app V b) =
    (adicLisseConstantUnit Y B).app ((proEtaleBaseChange i).op.obj V) b := by
  have h := ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B))
    ((proEtaleSheafDirectImage i CommRingCat.{u + 1}).obj
      (adicLisseConstantRing Y B))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange i).op
        (toSheafify (ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of B))))
  exact congrArg (fun f ↦ f.app V b) h

private def fixedDirectIso :
    sfbFixedScalarRestriction Y B ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} B) i ≅
      constantDirect i B ⋙ sfbFixedScalarRestriction X B := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun V ↦ ?_) ?_
    · refine
        { hom := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} B)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intro b x
                change (adicLisseConstantUnit Y B).app
                    ((proEtaleBaseChange i).op.obj V) b •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x) =
                  (proEtaleConstantDirectImageMap i CommRingCat.{u + 1}
                    (CommRingCat.of B)).hom.app V ((adicLisseConstantUnit X B).app V b) •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x)
                rw [constantDirect_section] }
          inv := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} B)
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intro b x
                change (proEtaleConstantDirectImageMap i CommRingCat.{u + 1}
                    (CommRingCat.of B)).hom.app V ((adicLisseConstantUnit X B).app V b) •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x) =
                  (adicLisseConstantUnit Y B).app
                    ((proEtaleBaseChange i).op.obj V) b •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x)
                rw [constantDirect_section] }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
    · intros; ext x; rfl
  · intros; ext V x; rfl

private theorem coefficient_unit :
    φ ≫ proEtaleConstantDirectImageMap i CommRingCat.{u + 1} (CommRingCat.of B) =
      (proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R ≫
        (proEtaleSheafDirectImage i CommRingCat.{u + 1}).map
          (globalCoefficient i R B φ) := by
  let a := proEtaleSheafAdjunction i CommRingCat.{u + 1}
  let ρ := proEtaleConstantDirectImageMap i CommRingCat.{u + 1} (CommRingCat.of B)
  change φ ≫ ρ = a.unit.app R ≫
    (proEtaleSheafDirectImage i CommRingCat.{u + 1}).map
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ ≫ _)
  have hn := a.unit.naturality φ
  change φ ≫ a.unit.app _ = a.unit.app R ≫
    (proEtaleSheafDirectImage i CommRingCat.{u + 1}).map
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).map φ) at hn
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  congr 1
  exact (a.homEquiv _ _).apply_symm_apply ρ |>.symm

private def coefficientDirectIso :
    constantDirect i B ⋙ SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) ≅
      SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (globalCoefficient i R B φ)) ⋙
        proEtaleRingModuleDirectImage i R
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
    · refine
        { hom := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} (R.obj.obj V))
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intro r x
                change (proEtaleConstantDirectImageMap i CommRingCat.{u + 1}
                    (CommRingCat.of B)).hom.app V (φ.hom.app V r) •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x) =
                  (globalCoefficient i R B φ).hom.app ((proEtaleBaseChange i).op.obj V)
                    (((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom.app V r) •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x)
                exact congrArg (fun b : (adicLisseRing Y B).obj.obj
                    ((proEtaleBaseChange i).op.obj V) ↦ b •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x))
                  (congrArg (fun f ↦ f.hom.app V r) (coefficient_unit i R B φ)) }
          inv := ConcreteCategory.ofHom (C := ModuleCat.{u + 1} (R.obj.obj V))
            { toFun := id
              map_add' := by intros; rfl
              map_smul' := by
                intro r x
                change (globalCoefficient i R B φ).hom.app ((proEtaleBaseChange i).op.obj V)
                    (((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app R).hom.app V r) •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x) =
                  (proEtaleConstantDirectImageMap i CommRingCat.{u + 1}
                    (CommRingCat.of B)).hom.app V (φ.hom.app V r) •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x)
                exact congrArg (fun b : (adicLisseRing Y B).obj.obj
                    ((proEtaleBaseChange i).op.obj V) ↦ b •
                      (show M.val.obj ((proEtaleBaseChange i).op.obj V) from x))
                  (congrArg (fun f ↦ f.hom.app V r) (coefficient_unit i R B φ)).symm }
          hom_inv_id := by ext x; rfl
          inv_hom_id := by ext x; rfl }
    · intros; ext x; rfl
  · intros; ext V x; rfl

private def globalTensorIso : completedAdicChange X φ ≅
    tensorFunctor.{u + 1, u + 1, u} φ := by
  change (completedAdicChangeData X φ).choose ≅ tensorFunctor.{u + 1, u + 1, u} φ
  let h := (completedAdicChangeData X φ).choose_spec.choose
  refine NatIso.ofComponents (fun M ↦ eqToIso (h M)) ?_
  intro M N f
  change (completedAdicChangeData X φ).choose.map f ≫ eqToHom (h N) =
    eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f
  rw [(completedAdicChangeData X φ).choose_spec.choose_spec.choose f]
  simp

private def localTensorIso : change i R B φ U ≅
    tensorFunctor.{u + 1, u + 1, u} (coefficient i R B φ U) := by
  letI := sourceExtensionDerived i R U
  letI := targetExtensionDerived B U
  let h := changeData i R B φ U
  refine NatIso.ofComponents (fun M ↦ eqToIso (h.obj_eq M)) ?_
  intro M N f
  change h.ordinary.map f ≫ eqToHom (h.obj_eq N) =
    eqToHom (h.obj_eq M) ≫ SheafOfModules.changeOfRingsHom (coefficient i R B φ U) M f
  rw [h.map_eq]
  simp

private def globalComparison :
    completedAdicChange X φ ⋙ sfbFixedScalarRestriction X B ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} B) i ≅
      proEtaleModuleInverseImage i R ⋙
        tensorFunctor.{u + 1, u + 1, u} (globalCoefficient i R B φ) ⋙
          sfbFixedScalarRestriction Y B := by
  let EX := fixedEquivalence X B
  let EY := fixedEquivalence Y B
  let P := SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
  let G := ProEtale.lowerStar (ModuleCat.{u + 1} B) i ⋙ EX.inverse ⋙ P
  let a := ((tensorAdjunction.{u + 1, u + 1, u} φ).ofNatIsoLeft
      (globalTensorIso R B φ).symm).comp
    (EX.toAdjunction.comp (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) i))
  let b := (proEtaleModuleInverseImageAdjunction i R).comp
    ((tensorAdjunction.{u + 1, u + 1, u}
      (globalCoefficient i R B φ)).comp EY.toAdjunction)
  let e : EY.functor ⋙ G ≅
      SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (globalCoefficient i R B φ)) ⋙
        proEtaleRingModuleDirectImage i R
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) :=
    Functor.isoWhiskerRight (fixedDirectIso i B) (EX.inverse ⋙ P) ≪≫
      Functor.isoWhiskerLeft (constantDirect i B)
        (Functor.isoWhiskerRight EX.unitIso.symm P) ≪≫
      coefficientDirectIso i R B φ
  let e' : G ≅ EY.inverse ⋙ _ :=
    Functor.isoWhiskerRight EY.counitIso.symm G ≪≫ Functor.isoWhiskerLeft EY.inverse e
  exact (a.ofNatIsoRight e').leftAdjointUniq b

section SliceComparison

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  {A S : Sheaf J CommRingCat.{u + 1}} (ψ : A ⟶ S) (V : C)
  [(J.over V).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify (J.over V) AddCommGrpCat.{u + 1}]

private abbrev ringSheaf (A : Sheaf J CommRingCat.{u + 1}) :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A

private def sliceSheafificationIso :
    PresheafOfModules.pushforward (F := Over.forget V) (𝟙 ((ringSheaf S).over V).obj) ⋙
        PresheafOfModules.sheafification (R := (ringSheaf S).over V) (𝟙 _) ≅
      PresheafOfModules.sheafification (R := ringSheaf S) (𝟙 _) ⋙
        SheafOfModules.overFunctor (ringSheaf S) V := by
  haveI (P : _root_.PresheafOfModules.{u + 1} (ringSheaf S).obj) :
      IsIso (SheafOfModules.overSheafificationMap (ringSheaf S) V P) :=
    SheafOfModules.overSheafificationMap_isIso (ringSheaf S) V P
  exact NatIso.ofComponents
    (fun P ↦ asIso (SheafOfModules.overSheafificationMap (ringSheaf S) V P))
    (fun f ↦ SheafOfModules.overSheafificationMap_naturality (ringSheaf S) V f)

private def sliceTensorPresheafIso :
    SheafOfModules.overFunctor (ringSheaf A) V ⋙
        tensorPresheafFunctor.{u + 1, u + 1, u}
          (((J.overPullback CommRingCat.{u + 1} V)).map ψ) ≅
      tensorPresheafFunctor.{u + 1, u + 1, u} ψ ⋙
        PresheafOfModules.pushforward (F := Over.forget V) (𝟙 _) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine PresheafOfModules.isoMk (fun W ↦ Iso.refl _) ?_
    intro W W' f
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
      change
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          ((J.overPullback CommRingCat.{u + 1} V).map ψ) (M.over V)).map f
            (s ⊗ₜ[_, _] m) =
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} ψ M).map
          ((Over.forget V).op.map f) (s ⊗ₜ[_, _] m)
      exact (tensorRestriction_tmul.{u + 1, u + 1, u}
        ((J.overPullback CommRingCat.{u + 1} V).map ψ) (M.over V) f s m).trans
        (tensorRestriction_tmul.{u + 1, u + 1, u} ψ M
          ((Over.forget V).op.map f) s m).symm
  · intros; ext W t; rfl

private def sliceTensorIso :
    tensorFunctor.{u + 1, u + 1, u} ψ ⋙
        SheafOfModules.overFunctor (ringSheaf S) V ≅
      SheafOfModules.overFunctor (ringSheaf A) V ⋙
        tensorFunctor.{u + 1, u + 1, u}
          ((J.overPullback CommRingCat.{u + 1} V).map ψ) :=
  (Functor.isoWhiskerRight (sliceTensorPresheafIso ψ V)
      (PresheafOfModules.sheafification (R := (ringSheaf S).over V) (𝟙 _)) ≪≫
    Functor.isoWhiskerLeft
      (tensorPresheafFunctor.{u + 1, u + 1, u} ψ)
      (sliceSheafificationIso (S := S) V)).symm

end SliceComparison

private def fixedSliceIso :
    sfbFixedScalarRestriction Y B ⋙
        (ProEt.topology Y).overPullback (ModuleCat.{u + 1} B) U ≅
      SheafOfModules.overFunctor (adicLisseRing Y B) U ⋙ sliceFixed B U :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; ext x; rfl)))
    (by intros; ext V x; rfl)

attribute [local irreducible] globalComparison fixedSliceIso sliceTensorIso localTensorIso
  tensorFunctor completedAdicChange change

/-- Ordinary scalar extension commutes with geometric inverse image and slice restriction,
including the specified constant B-action.

Source: Stacks Project, Modules on Sites, Tags 03D2, 03EL and 03EK;
Cohomology on Sites, lemma-pullback-tensor-product, the ordinary comparison used in
Tag 06YY. (auxiliary; not a blueprint node).

Proof: apply inverse image to the tensor presentation of scalar extension. Inverse
image preserves colimits and finite products, so it preserves the coequalizer imposing
additivity and R-balancing. Its canonical comparison therefore identifies the result
with extension of inverse-image modules along inverse image of φ. Transport the target
ring through the canonical constant-ring comparison. This map sends every original
constant b to the same constant b, so the identification is B-linear for the fixed
scalar actions. Slice restriction commutes with this tensor presentation: tensor
presheaves restrict termwise, and restriction commutes with sheafification. The map
on pure tensors is b tensor m sent to b tensor the inverse image of m, then restricted
to the slice. Its inverse is induced by the inverse tensor comparison. The balancing
relations give well-defined maps, the tensor universal property makes their composites
identities and proves naturality in the module. This works for B=0 and empty slices.
Only ordinary modules occur; no resolution, derived object or local isomorphism is
assumed or concluded. -/
theorem ordinaryComparison :
    Nonempty (completedAdicChange X φ ⋙ sfbFixedScalarRestriction X B ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} B) i ⋙
          (ProEt.topology Y).overPullback (ModuleCat.{u + 1} B) U) ≅
      restriction i R U ⋙ change i R B φ U ⋙ sliceFixed B U) :=
  ⟨Functor.isoWhiskerRight (globalComparison i R B φ)
      ((ProEt.topology Y).overPullback (ModuleCat.{u + 1} B) U) ≪≫
    Functor.isoWhiskerLeft
      (proEtaleModuleInverseImage i R ⋙
        tensorFunctor.{u + 1, u + 1, u} (globalCoefficient i R B φ))
      (fixedSliceIso B U) ≪≫
    Functor.isoWhiskerLeft (proEtaleModuleInverseImage i R)
      (Functor.isoWhiskerRight (sliceTensorIso (globalCoefficient i R B φ) U)
        (sliceFixed B U)) ≪≫
    Functor.isoWhiskerLeft (restriction i R U)
      (Functor.isoWhiskerRight (localTensorIso i R B φ U).symm (sliceFixed B U))⟩

end AlgebraicGeometry.Scheme.LocalScalar
