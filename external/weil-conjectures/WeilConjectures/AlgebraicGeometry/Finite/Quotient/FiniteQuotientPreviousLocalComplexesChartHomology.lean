/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Homology transport for the previous quotient chart model
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-previous-local-complexes-chart-homology).

The hard comparison step is isolated here: after restriction of scalars along
the quotient from the successor coefficient ring, the supplied chart
comparison identifies every slice homology object with the corresponding
constant realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] HasDerivedCategory.standard completedAdicChangeData

@[irreducible] private def restrictionCompIso (X : Scheme.{t})
    {R S T : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (α : R ⟶ S) (β : S ⟶ T) :
    SheafOfModules.restrictScalars.{t + 1} (α ≫ β) ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

@[irreducible] private def restrictionIdIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    SheafOfModules.restrictScalars.{t + 1} (𝟙 R) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsId'App _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

private theorem restrictionIsEquivalence (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{t + 1} e.hom).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (SheafOfModules.restrictScalars e.inv)
  · exact (restrictionIdIso X S).symm ≪≫
      eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) e.inv_hom_id.symm) ≪≫
      restrictionCompIso X e.inv e.hom
  · exact (restrictionCompIso X e.hom e.inv).symm ≪≫
      eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) e.hom_inv_id) ≪≫
      restrictionIdIso X R

private theorem changeIsEquivalence (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] : (completedAdicChange X φ).IsEquivalence := by
  let G := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
  have : G.IsEquivalence := restrictionIsEquivalence X
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso (asIso φ))
  let a := (completedAdjunction X φ).choose
  exact a.isEquivalence_left_of_isEquivalence_right

@[irreducible] private def derivedChangeComplexIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ]
    (K : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ) :
    (completedAdicDerivedChange X φ).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((completedAdicChange X φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  have := changeIsEquivalence X φ
  let F := completedAdicChange X φ
  let L := completedAdicDerivedChange X φ
  let ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (completedAdicChangeData X φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose
  have : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    (completedAdicChangeData X φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose_spec.1
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ _
  let i : L ≅ F.mapDerivedCategory :=
    Functor.leftDerivedNatIso L F.mapDerivedCategory ε F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)
  exact i.app _ ≪≫ F.mapDerivedCategoryFactors.app K

private abbrev baseConstantFunctor (X : Scheme.{t}) (B : Type t) [CommRing B] :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙ koszulConstantFunctor X B

private theorem baseConstantExact (X : Scheme.{t}) (B : Type t) [CommRing B] :
    (baseConstantFunctor X B).Additive ∧
      PreservesFiniteLimits (baseConstantFunctor X B) ∧
      PreservesFiniteColimits (baseConstantFunctor X B) := by
  have h := commutativeSiteConstantModuleFunctor_exact
    (ProEt.topology X) (ULift.{t + 1} B)
  have : (koszulConstantFunctor X B).Additive := h.1
  have : PreservesFiniteLimits (koszulConstantFunctor X B) := h.2.1
  have : PreservesFiniteColimits (koszulConstantFunctor X B) := h.2.2
  have : PreservesFiniteLimits (baseConstantFunctor X B) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (baseConstantFunctor X B) := comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

@[irreducible] private def constantRestrictionIso (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D] (f : B →+* D) (M : ModuleCat.{t} D) :
    (baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M) ≅
      (SheafOfModules.restrictScalars (adicModuleMap X f)).obj
        ((baseConstantFunctor X D).obj M) := by
  let α := koszulConstantUnit X B
  let β := koszulConstantUnit X D
  let φ := adicModuleMap X f
  have : Presheaf.IsLocallyInjective (ProEt.topology X) α :=
    (koszulConstantUnit_local X B).1
  have : Presheaf.IsLocallySurjective (ProEt.topology X) α :=
    (koszulConstantUnit_local X B).2
  have : Presheaf.IsLocallyInjective (ProEt.topology X) β :=
    (koszulConstantUnit_local X D).1
  have : Presheaf.IsLocallySurjective (ProEt.topology X) β :=
    (koszulConstantUnit_local X D).2
  let L := ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
  let L' := ModuleCat.uliftFunctor.{t + 1, t} D ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} D ≃+* D).toRingHom
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} B)).obj
    (L.obj ((ModuleCat.restrictScalars f).obj M))
  let P' := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} D)).obj
    (L'.obj M)
  let N := (baseConstantFunctor X D).obj M
  let a := (PresheafOfModules.sheafificationAdjunction β).unit.app P'
  let c : CommRingCat.of (ULift.{t + 1} B) ⟶ CommRingCat.of (ULift.{t + 1} D) :=
    CommRingCat.ofHom (RingHom.ulift f)
  let g : P ⟶ (PresheafOfModules.restrictScalars α).obj
      ((SheafOfModules.restrictScalars φ).obj N).val :=
    { app := fun U ↦ ModuleCat.ofHom (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars α).obj
          ((SheafOfModules.restrictScalars φ).obj N).val).obj U)
        { toFun := a.app U
          map_add' := (a.app U).hom.map_add
          map_smul' := fun b m ↦ by
            have hs : β.app U ((RingHom.ulift f) b) = φ.hom.app U (α.app U b) :=
              ConcreteCategory.congr_hom
                (NatTrans.congr_app (toSheafify_naturality (ProEt.topology X)
                  ((Functor.const X.ProEtᵒᵖ).map c)) U) b
            change a.app U ((RingHom.ulift f) b • (show P'.obj U from m)) =
              φ.hom.app U (α.app U b) • (show N.val.obj U from a.app U m)
            rw [← hs]
            exact (a.app U).hom.map_smul ((RingHom.ulift f) b) m }
      naturality := fun {U V} h ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact congrArg (fun k ↦ k m) (a.naturality h) }
  let e : (baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M) ⟶
      (SheafOfModules.restrictScalars φ).obj N :=
    (PresheafOfModules.sheafificationHomEquiv α).symm g
  have hfac : toSheafify (ProEt.topology X) P.presheaf ≫
      ((SheafOfModules.toSheaf _).map e).hom =
        (PresheafOfModules.toPresheaf _).map g := by
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv α (P := P)
        (F := (SheafOfModules.restrictScalars φ).obj N)).apply_symm_apply g)
  have : Presheaf.IsLocallyInjective (ProEt.topology X)
      ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallyInjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) P.presheaf))
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallySurjective (ProEt.topology X)
      (toSheafify (ProEt.topology X) P.presheaf))
  have : Presheaf.IsLocallyInjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (ProEt.topology X) _ hfac
  have : Presheaf.IsLocallySurjective (ProEt.topology X)
      ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (ProEt.topology X) hfac
  have : IsIso ((SheafOfModules.toSheaf _).map e) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (SheafOfModules.toSheaf _)
  exact asIso e

@[irreducible] private def changeUnitIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : R ⟶ S) [IsIso φ] :
    𝟭 _ ≅ completedAdicChange X φ ⋙ SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) := by
  have := changeIsEquivalence X φ
  let a := (completedAdjunction X φ).choose
  exact asIso a.unit

@[irreducible] private def coefficientRestrictionIso (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
    [IsIso φB] [IsIso φD] (f : B →+* D) (ψ : R ⟶ S)
    (h : adicConstantMap X f ≫ φD = φB ≫ ψ) (M : ModuleCat.{t} D) :
    (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ)).obj
        ((finiteCoefficientConstantFunctor X D φD).obj M) ≅
      (finiteCoefficientConstantFunctor X B φB).obj ((ModuleCat.restrictScalars f).obj M) := by
  let H := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})
  let G := SheafOfModules.restrictScalars.{t + 1} (H.map φB)
  have : G.IsEquivalence := restrictionIsEquivalence X (H.mapIso (asIso φB))
  have hh : H.map φB ≫ H.map ψ = adicModuleMap X f ≫ H.map φD := by
    change H.map φB ≫ H.map ψ = H.map (adicConstantMap X f) ≫ H.map φD
    rw [← H.map_comp, ← H.map_comp, h]
  apply G.preimageIso
  exact ((restrictionCompIso X (H.map φB) (H.map ψ)).app _).symm ≪≫
    (eqToIso (congrArg (SheafOfModules.restrictScalars.{t + 1}) hh)).app _ ≪≫
    (restrictionCompIso X (adicModuleMap X f) (H.map φD)).app _ ≪≫
    (SheafOfModules.restrictScalars (adicModuleMap X f)).mapIso
      (((changeUnitIso X φD).app ((baseConstantFunctor X D).obj M)).symm) ≪≫
    (constantRestrictionIso X f M).symm ≪≫
    (changeUnitIso X φB).app
      ((baseConstantFunctor X B).obj ((ModuleCat.restrictScalars f).obj M))

@[irreducible] private def representativeHomologyIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor D q).obj
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≅
      F.obj ((DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj K)) :=
  (DerivedCategory.homologyFunctorFactors D q).app _ ≪≫
    (K.sc q).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C q).app K).symm

@[irreducible] private def sliceHomologyIso (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (K : DerivedCategory (SheafOfModules.{t + 1} R)) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
        (ringedSiteDerivedRestrictionOfUniverses R U K) ≅
      (SheafOfModules.overFunctor R U).obj
        ((DerivedCategory.homologyFunctor _ q).obj K) := by
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact representativeHomologyIso (SheafOfModules.overFunctor R U)
    (DerivedCategory.Q.objPreimage K) q ≪≫
      (SheafOfModules.overFunctor R U).mapIso
        ((DerivedCategory.homologyFunctor _ q).mapIso (DerivedCategory.Q.objObjPreimageIso K))

@[irreducible] private def modelHomologyIso (X : Scheme.{t}) (B : Type t) [CommRing B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    {R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicConstantRing X B ⟶ R) [IsIso φ]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((completedAdicDerivedChange X φ).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))) ≅
      (finiteCoefficientConstantFunctor X B φ).obj (P.homology q) := by
  have := changeIsEquivalence X φ
  have := (baseConstantExact X B).1
  have := (baseConstantExact X B).2.1
  have := (baseConstantExact X B).2.2
  exact (DerivedCategory.homologyFunctor _ q).mapIso
      (derivedChangeComplexIso X φ (finiteModelConstantComplex X B P)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
    ((finiteModelConstantComplex X B P).sc q).mapHomologyIso (completedAdicChange X φ) ≪≫
    (completedAdicChange X φ).mapIso ((P.sc q).mapHomologyIso (baseConstantFunctor X B))

private abbrev restrictedObject (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (ψ : R ⟶ S)
    (K : DerivedCategory (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))) :=
  let F := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map ψ)
  DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
    (DerivedCategory.Q.objPreimage K))

private theorem chartHomology (X : Scheme.{t})
    {B D : Type t} [CommRing B] [CommRing D]
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φB : adicConstantRing X B ⟶ R) (φD : adicConstantRing X D ⟶ S)
    [IsIso φB] [IsIso φD] (f : B →+* D) (ψ : R ⟶ S)
    (h : adicConstantMap X f ≫ φD = φB ≫ ψ)
    (K : DerivedCategory (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)))
    (P : CochainComplex (ModuleCat.{t} D) ℤ) (U : X.ProEt)
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses _ U K ≅
        ringedSiteDerivedRestrictionOfUniverses _ U
          ((completedAdicDerivedChange X φD).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X D P)))))
    (q : ℤ) :
    Nonempty
      ((SheafOfModules.overFunctor _ U).obj
          ((DerivedCategory.homologyFunctor _ q).obj (restrictedObject X ψ K)) ≅
        (SheafOfModules.overFunctor _ U).obj
          ((finiteCoefficientConstantFunctor X B φB).obj
            ((((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj P).homology
              q))) := by
  let H := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})
  let L := (completedAdicDerivedChange X φD).obj
    (DerivedCategory.Q.obj (finiteModelConstantComplex X D P))
  let α := H.map ψ
  let F := SheafOfModules.restrictScalars.{t + 1} α
  let O := SheafOfModules.overFunctor.{t + 1} (H.obj S) U
  let O' := SheafOfModules.overFunctor.{t + 1} (H.obj R) U
  let FU := SheafOfModules.restrictScalars.{t + 1}
    (((ProEt.topology X).overPullback RingCat.{t + 1} U).map α)
  obtain ⟨hlim, hcolim, _⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction ψ
  have : PreservesFiniteLimits F := hlim
  have : PreservesFiniteColimits F := hcolim
  let eH : O.obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      O.obj ((finiteCoefficientConstantFunctor X D φD).obj (P.homology q)) :=
    (sliceHomologyIso X _ U K q).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e.some ≪≫
      sliceHomologyIso X _ U L q ≪≫ O.mapIso (modelHomologyIso X D φD P q)
  let ePrevious : (DerivedCategory.homologyFunctor _ q).obj (restrictedObject X ψ K) ≅
      F.obj ((DerivedCategory.homologyFunctor _ q).obj K) :=
    representativeHomologyIso F (DerivedCategory.Q.objPreimage K) q ≪≫
      F.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso
        (DerivedCategory.Q.objObjPreimageIso K))
  exact ⟨O'.mapIso ePrevious ≪≫ FU.mapIso eH ≪≫
    O'.mapIso (coefficientRestrictionIso X φB φD f ψ h (P.homology q)) ≪≫
    O'.mapIso ((finiteCoefficientConstantFunctor X B φB).mapIso
      ((P.sc q).mapHomologyIso (ModuleCat.restrictScalars f)).symm)⟩

/-- Transport the supplied chart comparison to homology after restriction of scalars.

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
The quotient map from `A ⧸ I^(n+2)` to `A ⧸ I^(n+1)` is exact on modules,
slice restriction, and constant realization. Applying the derived homology
functor to the supplied comparison and composing the coefficient compatibility
isomorphisms gives the displayed isomorphism in every degree.
(blueprint: lem-weil-pbc-finite-quotient-previous-local-complexes-chart-homology).
-/
theorem finiteQuotient_previous_local_complexes_chart_homology
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (V : X.Etale) (W Z : X.Etale) (g : W ⟶ V) (f : Z ⟶ W)
    (a b : ℤ) (hab : a ≤ b) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ)
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj Z) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj Z) ((completedAdicDerivedChange X (φ n)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    let qring : A ⧸ d.ideal ^ (n + 1 + 1) →+* A ⧸ d.ideal ^ (n + 1) :=
      Ideal.Quotient.factorPowSucc d.ideal (n + 1)
    let Q := ((ModuleCat.restrictScalars qring).mapHomologicalComplex (.up ℤ)).obj P
    ∀ q : ℤ, Nonempty
      ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            (finiteQuotientPreviousObject X d M n)) ≅
        (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((finiteCoefficientConstantFunctor X
            (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))).obj (Q.homology q))) := by
  let _ := g
  let _ := f
  let _ := hab
  have : IsIso (φ n) := hφ n
  have : IsIso (φ (n + 1)) := hφ (n + 1)
  exact chartHomology X (φ (n + 1)) (φ n)
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))
    (hcompat.1 n) ((completedAdicQuotientReduction X d n).obj M) P
    ((toProEt X).obj Z) e

end AlgebraicGeometry.Scheme
