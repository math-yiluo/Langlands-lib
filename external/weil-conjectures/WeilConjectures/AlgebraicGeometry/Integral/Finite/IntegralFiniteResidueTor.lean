/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteResidueNormalization
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian

import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import Mathlib.CategoryTheory.Sites.Adjunction
import all WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitudeResidue

/-! # Tor intervals of finite integral reductions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open Opposite
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint Mod.monoidalClosed
attribute [local instance 20000] sheafBraidedCategory

open FiniteDiscreteOrdinary

private abbrev fixedFunctor (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) (e : Encoding A X) :=
  sectionEncoding A X e.ringIso ⋙ fixedRestriction A X

private theorem fixedFunctor_eq (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) (e : Encoding A X) :
    fixedFunctor A X e = e.ordinary.functor ⋙ e.fixed.functor := by
  rw [e.ordinary_functor, e.fixed_functor]

private theorem constant_scalar_unit (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] (U : X.ProEtᵒᵖ) (a : A) :
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of A)).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app U a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).app U a := by
  let J := Scheme.ProEt.topology X
  have hc := toSheafify_naturality J
    (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv
  change ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)) ≫
    sheafifyMap J (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv ≫
    (sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))).hom).app U) a = _
  erw [← Category.assoc, ← hc, Category.assoc, sheafComposeIso_hom_fac]
  rfl

private theorem fixed_scalar
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : Encoding A X) (M : Internal A X)
    (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} A) (x : M.X.obj.obj U) :
    @SMul.smul _ _ (((fixedFunctor A X e).obj M).obj.obj U).isModule.toSMul a x =
      @SMul.smul _ _
        (((InternalAbelianSheafModule.sectionModuleEquivalence
          (Scheme.ProEt.topology X) (condensedRingObj (coefficient A) X)).functor.obj M).val.obj
            U).isModule.toSMul
          (e.ringIso.hom.hom.app U
            ((toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj
                (CommRingCat.of (ULift.{u + 1} A)))).app U a)) x := by
  unfold fixedFunctor
  change @SMul.smul _ _
    (((InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology X) (condensedRingObj (coefficient A) X)).functor.obj M).val.obj
        U).isModule.toSMul
      (e.ringIso.hom.hom.app U
        (((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
            (CommRingCat.of (ULift.{u + 1} A))).hom.app U
              ((toSheafify (Scheme.ProEt.topology X)
                ((Functor.const X.ProEtᵒᵖ).obj
                  (RingCat.of (ULift.{u + 1} A)))).app U a))) x = _
  rw [constant_scalar_unit]

-- Comparing the iterated scalar-restriction structures needs additional reduction.
private def fixedRestrictionSquare
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (X : Scheme.{u}) (eA : Encoding A X) (eB : Encoding B X)
    (ρ : condensedRingObj (coefficient A) X ⟶ condensedRingObj (coefficient B) X)
    [IsMonHom ρ] (φ : ULift.{u + 1} A →+* ULift.{u + 1} B)
    (hρ : ∀ (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} A),
      ρ.hom.app U ((canonicalAbelianMap A X).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) =
      (canonicalAbelianMap B X).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app U (φ a))) :
    Mod.comap ρ ⋙ fixedFunctor A X eA ≅ fixedFunctor B X eB ⋙
      sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) := by
  have hs (N : Internal B X) (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} A)
      (x : N.X.obj.obj U) :
      @SMul.smul _ _
        (((fixedFunctor A X eA).obj ((Mod.comap ρ).obj N)).obj.obj U).isModule.toSMul a x =
      @SMul.smul _ _ (((fixedFunctor B X eB).obj N).obj.obj U).isModule.toSMul (φ a) x := by
    erw [fixed_scalar A X eA ((Mod.comap ρ).obj N) U a x,
      fixed_scalar B X eB N U (φ a) x]
    rw [eA.normalization, eB.normalization]
    let r := (canonicalAbelianMap A X).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)
    have hμ := congr_app (Functor.LaxMonoidal.μ_natural_left
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ρ N.X) U
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f ≫ (Mod.act N.X).hom.app U) hμ) (r ⊗ₜ[ℤ] x)
    change (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X)
      Ab.{u + 1}) (condensedRingObj (coefficient A) X) N.X).app U) ≫
        ((ρ ▷ N.X).hom.app U) ≫ (Mod.act N.X).hom.app U) (r ⊗ₜ[ℤ] x) = _
    rw [← hρ U a]
    exact hh.symm
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · exact
      { hom := { hom :=
          { app := fun U ↦ ModuleCat.ofHom
              (X := ((fixedFunctor A X eA).obj ((Mod.comap ρ).obj N)).obj.obj U)
              (Y := (ModuleCat.restrictScalars.{u + 1} φ).obj
                (((fixedFunctor B X eB).obj N).obj.obj U))
              { toFun := fun x ↦ x
                map_add' := fun _ _ ↦ rfl
                map_smul' := fun a x ↦ hs N U a x }
            naturality := by intros; ext x; rfl } }
        inv := { hom :=
          { app := fun U ↦ ModuleCat.ofHom
              (X := (ModuleCat.restrictScalars.{u + 1} φ).obj
                (((fixedFunctor B X eB).obj N).obj.obj U))
              (Y := ((fixedFunctor A X eA).obj ((Mod.comap ρ).obj N)).obj.obj U)
              { toFun := fun x ↦ x
                map_add' := fun _ _ ↦ rfl
                map_smul' := fun a x ↦ (hs N U a x).symm }
            naturality := by intros; ext x; rfl } }
        hom_inv_id := by ext U x; rfl
        inv_hom_id := by ext U x; rfl }
  · intros
    ext U x
    rfl

private theorem homology_bounds {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : _root_.DerivedCategory C) (a b : ℤ) :
    _root_.DerivedCategory.homologyConcentratedIn a b K ↔
      ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor C q).obj K) := by
  constructor
  · rintro ⟨hlo, hhi⟩ q (hq | hq)
    · exact (_root_.DerivedCategory.isGE_iff K a).mp hlo q hq
    · exact (_root_.DerivedCategory.isLE_iff K b).mp hhi q hq
  · intro h
    exact ⟨(_root_.DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ h q (.inl hq)),
      (_root_.DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ h q (.inr hq))⟩

private theorem native_residue_test
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    [TopologicalSpace B] [IsTopologicalRing B] [Finite B] [DiscreteTopology B]
    (X : Scheme.{u}) (eA : Encoding A X) (eB : Encoding B X)
    (ρ : condensedRingObj (coefficient A) X ⟶ condensedRingObj (coefficient B) X)
    [IsMonHom ρ] (φ : ULift.{u + 1} A →+* ULift.{u + 1} B)
    (hsq : Mod.comap ρ ⋙ fixedFunctor A X eA ≅ fixedFunctor B X eB ⋙
      sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ))
    (r : ULift.{u + 1} A) (hr : IsNilpotent r) [(Ideal.span {r}).IsMaximal]
    (eκ : ModuleCat.of (ULift.{u + 1} A) ((ULift.{u + 1} A) ⧸ Ideal.span {r}) ≅
      (ModuleCat.restrictScalars.{u + 1} φ).obj
        (ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B)))
    (L : _root_.DerivedCategory (Internal A X)) (a b : ℤ) (hab : a ≤ b)
    (hb : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((Mod.extendScalars ρ).leftDerivedFunctor.obj L))) :
    _root_.DerivedCategory.torAmplitudeIn (Internal A X) a b L := by
  let J := Scheme.ProEt.topology X
  let FA := eA.ordinary.functor ⋙ eA.fixed.functor
  let FB := eB.ordinary.functor ⋙ eB.fixed.functor
  have hsq' : Mod.comap ρ ⋙ FA ≅ FB ⋙
      sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ) := by
    simpa only [fixedFunctor_eq] using hsq
  obtain ⟨mBo⟩ := ordinary_monoidal B X eB
  obtain ⟨mBf⟩ := fixed_monoidal B X eB
  let := mBo
  let := mBf
  let : FB.Monoidal := by dsimp only [FB]; infer_instance
  obtain ⟨⟨mAd⟩, _, ht⟩ := encoding_tensor_tor A X eA
  let := mAd
  let : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let κ := (Mod.comap ρ).obj (Mod.regular (condensedRingObj (coefficient B) X))
  let ec : FA.obj κ ≅ (constantSheaf J (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
      (ModuleCat.of (ULift.{u + 1} A) ((ULift.{u + 1} A) ⧸ Ideal.span {r})) :=
    hsq'.app _ ≪≫
      (sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ)).mapIso
        ((Functor.Monoidal.εIso FB).symm ≪≫
          Functor.Monoidal.εIso (presheafToSheaf J
            (ModuleCat.{u + 1} (ULift.{u + 1} B)))) ≪≫
      (constantCommuteCompose J (ModuleCat.restrictScalars.{u + 1} φ)).app
        (ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B)) ≪≫
      (constantSheaf J (ModuleCat.{u + 1} (ULift.{u + 1} A))).mapIso eκ.symm
  obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat
    (_root_.DerivedCategory.Q.objPreimage L)
  have : QuasiIso π := hπ
  let eL := asIso (_root_.DerivedCategory.Q.map π) ≪≫
    _root_.DerivedCategory.Q.objObjPreimageIso L
  have : IsIso (Mod.KFlatScalarTower.computationRight ρ P) :=
    Mod.KFlatScalarTower.computationRight_isIso ρ P hP
  let en : (Mod.comap ρ).mapDerivedCategory.obj
      ((Mod.extendScalars ρ).leftDerivedFunctor.obj L) ≅
      L ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj κ :=
    (Mod.comap ρ).mapDerivedCategory.mapIso
      ((Mod.extendScalars ρ).leftDerivedFunctor.mapIso eL.symm) ≪≫
    asIso (Mod.KFlatScalarTower.computationRight ρ P) ≪≫
    (_root_.DerivedCategory.QObjTensorSingleFunctorObjIso P hP κ).symm ≪≫
    whiskerRightIso eL _
  let ed : eA.fixedDerived.functor.obj
      ((Mod.comap ρ).mapDerivedCategory.obj
        ((Mod.extendScalars ρ).leftDerivedFunctor.obj L)) ≅
      eA.fixedDerived.functor.obj L ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf J (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
          (ModuleCat.of (ULift.{u + 1} A) ((ULift.{u + 1} A) ⧸ Ideal.span {r}))) :=
    eA.fixedDerived.functor.mapIso en ≪≫
      (Functor.Monoidal.μIso eA.fixedDerived.functor L
        ((_root_.DerivedCategory.singleFunctor _ 0).obj κ)).symm ≪≫
      tensorIso (Iso.refl _) ((FA.mapDerivedCategorySingleFunctor 0).app κ ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso ec)
  have hn := (homology_bounds _ a b).mpr hb
  have hf := FA.homologyConcentratedIn_mapDerivedCategory_obj
    ((Mod.comap ρ).homologyConcentratedIn_mapDerivedCategory_obj hn)
  apply (ht L a b hab).mpr
  apply (DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor r hr a b _).mpr
  exact (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso ed hf

private theorem canonicalAbelianMap_natural
    (A B : Type u) [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (f : ULift.{u + 1} A →+ ULift.{u + 1} B)
    (g : coefficient A ⟶ coefficient B)
    (h : pointConstants A ≫ g.hom =
      (Functor.const Profinite.{u}ᵒᵖ).map (AddCommGrpCat.ofHom f) ≫ pointConstants B)
    (X : Scheme.{u}) :
    canonicalAbelianMap A X ≫ (upperStarFromPoint X).map g =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom f) ≫ canonicalAbelianMap B X := by
  let J := coherentTopology Profinite.{u}
  let eA := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (coefficient A)).symm (pointConstants A)
  let eB := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
    (coefficient B)).symm (pointConstants B)
  have hA : toSheafify J ((Functor.const _).obj
      (AddCommGrpCat.of (ULift.{u + 1} A))) ≫ eA.hom = pointConstants A :=
    ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hB : toSheafify J ((Functor.const _).obj
      (AddCommGrpCat.of (ULift.{u + 1} B))) ≫ eB.hom = pointConstants B :=
    ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _
  have he : eA ≫ g = (constantSheaf J Ab.{u + 1}).map
      (AddCommGrpCat.ofHom f) ≫ eB := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (coefficient B).property
    change _ ≫ (eA.hom ≫ g.hom) = _ ≫ (_ ≫ eB.hom)
    change (toSheafify J _ ≫ eA.hom) ≫ g.hom =
      (toSheafify J _ ≫ sheafifyMap J
        ((Functor.const Profinite.{u}ᵒᵖ).map (AddCommGrpCat.ofHom f))) ≫ eB.hom
    rw [hA, ← toSheafify_naturality, Category.assoc, hB]
    exact h
  change (constantSchemeIso X).hom.app _ ≫ (upperStarFromPoint X).map eA ≫
    (upperStarFromPoint X).map g = _
  rw [← Functor.map_comp, he, Functor.map_comp]
  erw [← Category.assoc,
    ← (constantSchemeIso X).hom.naturality (AddCommGrpCat.ofHom f)]
  rfl

private def residueHom (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : ∀ n : ℕ,
    Padic.coefficientExtensionRing l E (n + 1) →+* Padic.coefficientExtensionRing l E 1
  | 0 => RingHom.id _
  | n + 1 => (residueHom l E n).comp (Padic.coefficientExtensionTransition l E (n + 1))

private theorem residueHom_mk (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (x : Padic.coefficientExtensionIntegers l E) :
    residueHom l E n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1) x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem residue_constants (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))),
      (integralResidueTransition l E X n).hom.app U
        ((canonicalAbelianMap (Padic.coefficientExtensionRing l E (n + 1)) X).hom.app U
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U a)) =
      (canonicalAbelianMap (Padic.coefficientExtensionRing l E 1) X).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E 1))))).app U
              (ULift.up (residueHom l E n a.down))) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    let A := Padic.coefficientExtensionRing l E (n + 2)
    let B := Padic.coefficientExtensionRing l E (n + 1)
    let f : ULift.{u + 1} A →+ ULift.{u + 1} B :=
      (ULift.ringEquiv.symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          ULift.ringEquiv.toRingHom)).toAddMonoidHom
    have hp : pointConstants A ≫ (AdicCompletion.transitionRing l E n).hom =
        (Functor.const Profinite.{u}ᵒᵖ).map (AddCommGrpCat.ofHom f) ≫ pointConstants B := by
      ext S a
      rfl
    have ht := canonicalAbelianMap_natural A B f (AdicCompletion.transitionRing l E n) hp X
    intro U a
    have he := congrArg (fun k ↦ k.hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) ht
    have hu := ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom f))) U) a
    change (AdicCompletion.transition l E X n).hom.app U
      ((canonicalAbelianMap A X).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) =
      (canonicalAbelianMap B X).hom.app U
        (((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.ofHom f)).hom.app U
            ((toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) at he
    change (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app U (f a) =
        (((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.ofHom f)).hom.app U
            ((toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)) at hu
    rw [← hu] at he
    change (integralResidueTransition l E X n).hom.app U
      ((AdicCompletion.transition l E X n).hom.app U _) = _
    rw [he, ih]
    rfl

/-- A ring isomorphism from the quotient by `r` that intertwines the given ring map is
a linear isomorphism onto the restricted regular module. -/
private def residueModuleIso {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    (r : R) (e : (R ⧸ Ideal.span {r}) ≃+* S)
    (he : ∀ a : R, e (Ideal.Quotient.mk _ a) = φ a) :
    ModuleCat.of R (R ⧸ Ideal.span {r}) ≅
      (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of S S) :=
  (show ModuleCat.of R (R ⧸ Ideal.span {r}) ≃ₗ[R]
      (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of S S) from
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        change e (Ideal.Quotient.mk _ a * x) = φ a * e x
        rw [map_mul, he] }).toModuleIso

-- Match the native derived tensor structures with their normalized finite encodings.
/-- Over a finite coefficient quotient, the cohomological interval of the canonical
residue scalar extension tests the Tor interval of a bounded constructible complex. -/
theorem integral_finite_residue_tor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n)))
    (hc : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) X L)
    (a b : ℤ) (hab : a ≤ b)
    (hbound : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Mod.extendScalars (integralResidueTransition l E X n)).leftDerivedFunctor.obj L))) :
    DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)) a b L := by
  have _hc := hc
  -- The nilpotent residue criterion holds directly on the pro-etale site.
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := Padic.coefficientExtensionRing l E 1
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : Finite B := Padic.finite_coefficientExtensionRing l E 1 (by omega)
  let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E (n + 1)
  let : DiscreteTopology B := DerivedNakayama.quotientDiscrete l E 1
  obtain ⟨eA⟩ := encoding_exists A X
  obtain ⟨eB⟩ := encoding_exists B X
  let φ : ULift.{u + 1} A →+* ULift.{u + 1} B :=
    ULift.ringEquiv.symm.toRingHom.comp ((residueHom l E n).comp ULift.ringEquiv.toRingHom)
  let r₀ : A := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (Padic.coefficientExtensionUniformizer l E)
  let r : ULift.{u + 1} A := ULift.up r₀
  have hr₀ : r₀ ^ (n + 1) = 0 := by
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hr : IsNilpotent r := ⟨n + 1, by
    change ULift.up (r₀ ^ (n + 1)) = ULift.up 0
    rw [hr₀]⟩
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let : (Ideal.span {Padic.coefficientExtensionUniformizer l E}).IsMaximal := by
    rw [hgen]
    exact hmax
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    (m := Ideal.span {Padic.coefficientExtensionUniformizer l E})
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact Ideal.pow_le_self (by omega))
  have hm₀ : (Ideal.span {r₀}).IsMaximal := by
    simpa only [Ideal.map_span, Set.image_singleton] using hm
  have hm' := hm₀.map_bijective (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A)
    ULift.ringEquiv.symm.bijective
  have : (Ideal.span {r}).IsMaximal := by
    simpa [Ideal.map_span, r, ULift.ringEquiv] using hm'
  let e : ((ULift.{u + 1} A) ⧸ Ideal.span {r}) ≃+* ULift.{u + 1} B :=
    (Ideal.quotientEquiv (Ideal.span {r}) (Ideal.span {r₀}) ULift.ringEquiv
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)).trans
        ((integralResidueQuotientEquiv l E n).trans ULift.ringEquiv.symm)
  have he (a : ULift.{u + 1} A) : e (Ideal.Quotient.mk _ a) = φ a := by
    rcases a with ⟨a⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    change ULift.up (integralResidueQuotientEquiv l E n
      (Ideal.Quotient.mk _
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x))) =
      ULift.up (residueHom l E n
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x))
    rw [integralResidueQuotientEquiv_mk, residueHom_mk]
  let eκ := residueModuleIso φ r e he
  exact native_residue_test A B X eA eB (integralResidueTransition l E X n) φ
    (fixedRestrictionSquare A B X eA eB (integralResidueTransition l E X n) φ
      (residue_constants l E X n)) r hr eκ L a b hab hbound

end AlgebraicGeometry.ProEtale
