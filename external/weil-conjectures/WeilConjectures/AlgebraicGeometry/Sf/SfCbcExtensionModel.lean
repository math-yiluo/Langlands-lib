/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionTower
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCompletionReduction
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.CategoryTheory.AdicSites.SmallSiteReducedCompletionUnit
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteEquivalenceTensor
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact extension and resolving models for completed extension by zero

## References

* Stacks Project Tags 099M, 099N and 0941
* Stacks Tags 098K and 00VC
* Stacks Tag 00XZ
* Stacks Tag 03D1
* Stacks 05RU
* Stacks Tags 06YS, 03DI and 0E8I
* Stacks Tags 03DJ and 0941
* Stacks Tags 099M and 06YY
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem sfCbcWeakSheafifyProEt (X : Scheme.{t}) :
    HasWeakSheafify (ProEt.topology X) CommRingCat.{t + 1} := inferInstance

private theorem sfCbcWeakSheafifyOver (X : Scheme.{t}) (W : X.ProEt) :
    HasWeakSheafify ((ProEt.topology X).over W) CommRingCat.{t + 1} := inferInstance

private theorem sfCbcWeakSheafifyModel (X : Scheme.{t}) :
    HasWeakSheafify (proEtaleModelTopology X) CommRingCat.{t + 1} := inferInstance

private theorem sfCbcSheafifyHomExt
    {C D : Type*} [Category C] [Category D] (J : GrothendieckTopology C)
    [HasWeakSheafify J D] {P : Cᵒᵖ ⥤ D} {Q : Sheaf J D}
    (f g : (presheafToSheaf J D).obj P ⟶ Q)
    (h : ∀ V, (toSheafify J P).app V ≫ f.hom.app V =
      (toSheafify J P).app V ≫ g.hom.app V) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ Q.property
  ext V
  exact h V

private theorem sfCbcSheafificationCompatibility_app
    {C D A : Type*} [Category C] [Category D] [Category A]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] [G.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension F]
    [HasWeakSheafify J A] [HasWeakSheafify K A] (P : Dᵒᵖ ⥤ A) (V : Cᵒᵖ) :
    (toSheafify J (G.op ⋙ P)).app V ≫
        ((G.pushforwardContinuousSheafificationCompatibility A J K).app P).hom.hom.app V =
      (toSheafify K P).app (G.op.obj V) :=
  congrArg (fun f ↦ f.app V)
    (G.toSheafify_pullbackSheafificationCompatibility A J K P)

private theorem sfCbcSheafIso_hom_inv
    {C A : Type*} [Category C] [Category A] {J : GrothendieckTopology C}
    {P Q : Sheaf J A} (e : P ≅ Q) (V : Cᵒᵖ) :
    e.hom.hom.app V ≫ e.inv.hom.app V = 𝟙 (P.obj.obj V) :=
  congrArg (fun f ↦ f.hom.app V) e.hom_inv_id

private theorem sfCbcUnitIsoComposite
    {C : Type*} [Category C] {P Q R S : C}
    (η : P ⟶ Q) (a : Q ⟶ R) (b : R ⟶ Q) (c : Q ⟶ S)
    (f : P ⟶ R) (g : P ⟶ S)
    (ha : η ≫ a = f) (hi : a ≫ b = 𝟙 Q) (hc : η ≫ c = g) :
    f ≫ (b ≫ c) = g := by
  rw [← ha, Category.assoc, ← Category.assoc a, hi, Category.id_comp, hc]

private theorem sfCbcSlice_cocontinuous (X : Scheme.{t}) (W : X.ProEt) :
    (cbcSliceFunctor X W).IsCocontinuous ((ProEt.topology X).over W)
      (ProEt.topology W.left) := by
  let e := ProEt.sliceEquiv X W
  let := ProEt.sliceDense X W
  have h := Equivalence.eq_inducedTopology_of_isDenseSubsite ((ProEt.topology X).over W)
    (ProEt.topology W.left) e
  change e.functor.IsCocontinuous _ _
  rw [h]
  exact inferInstanceAs (e.functor.IsCocontinuous ((ProEt.topology X).over W)
    (e.inverse.inducedTopology ((ProEt.topology X).over W)))

private def sfCbcConstantSliceIso (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] :
    (adicConstantRing X A).over W ≅
      ((cbcSliceFunctor X W).sheafPushforwardContinuous CommRingCat.{t + 1}
        ((ProEt.topology X).over W) (ProEt.topology W.left)).obj
          (adicConstantRing W.left A) := by
  letI : HasWeakSheafify (ProEt.topology X) CommRingCat.{t + 1} := sfCbcWeakSheafifyProEt X
  letI : HasWeakSheafify (ProEt.topology W.left) CommRingCat.{t + 1} :=
    sfCbcWeakSheafifyProEt W.left
  letI : HasWeakSheafify ((ProEt.topology X).over W) CommRingCat.{t + 1} :=
    sfCbcWeakSheafifyOver X W
  let := sfCbcSlice_cocontinuous X W
  exact (((Over.forget W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology X)).app
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A)))).symm ≪≫
    ((cbcSliceFunctor X W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology W.left)).app
        ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A)))

private theorem sfCbcConstantSliceIso_unit (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] (V : Over W) :
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A)))).app
        (op V.left) ≫ (sfCbcConstantSliceIso X W A).hom.hom.app (op V) =
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A)))).app
          (op ((cbcSliceFunctor X W).obj V)) := by
  let : HasWeakSheafify (ProEt.topology X) CommRingCat.{t + 1} := sfCbcWeakSheafifyProEt X
  let : HasWeakSheafify (ProEt.topology W.left) CommRingCat.{t + 1} := sfCbcWeakSheafifyProEt W.left
  let : HasWeakSheafify ((ProEt.topology X).over W) CommRingCat.{t + 1} := sfCbcWeakSheafifyOver X W
  let := sfCbcSlice_cocontinuous X W
  let P := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))
  let P' := (Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))
  let e₀ := ((Over.forget W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology X)).app P
  let e₁ := ((cbcSliceFunctor X W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology W.left)).app P'
  have h := sfCbcSheafificationCompatibility_app (Over.forget W)
    ((ProEt.topology X).over W) (ProEt.topology X) P (op V)
  have hi := sfCbcSheafIso_hom_inv e₀ (op V)
  change (toSheafify (ProEt.topology X) P).app (op V.left) ≫
    (e₀.inv.hom.app (op V) ≫ e₁.hom.hom.app (op V)) = _
  exact sfCbcUnitIsoComposite _ (e₀.hom.hom.app (op V)) (e₀.inv.hom.app (op V))
    (e₁.hom.hom.app (op V)) _ _ h hi
    (sfCbcSheafificationCompatibility_app (cbcSliceFunctor X W)
      ((ProEt.topology X).over W) (ProEt.topology W.left) P' (op V))

/-- Constant sections uniquely identify the coefficient sheaf on the localized site. -/
theorem sfCbcConstantSliceMap_existsUnique (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] :
    ∃! φ : (adicConstantRing X A).over W ⟶
        ((cbcSliceFunctor X W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology X).over W) (ProEt.topology W.left)).obj
            (adicConstantRing W.left A),
      ∀ V : Over W,
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app (op V.left) ≫
              φ.hom.app (op V) =
        (toSheafify (ProEt.topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app
              (op ((cbcSliceFunctor X W).obj V)) := by
  let : HasWeakSheafify (ProEt.topology X) CommRingCat.{t + 1} := sfCbcWeakSheafifyProEt X
  let : HasWeakSheafify (ProEt.topology W.left) CommRingCat.{t + 1} := sfCbcWeakSheafifyProEt W.left
  let : HasWeakSheafify ((ProEt.topology X).over W) CommRingCat.{t + 1} := sfCbcWeakSheafifyOver X W
  let e := sfCbcConstantSliceIso X W A
  refine ⟨e.hom, sfCbcConstantSliceIso_unit X W A, ?_⟩
  intro c hc
  let e₀ := ((Over.forget W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A)))
  apply (cancel_epi e₀.hom).mp
  apply sfCbcSheafifyHomExt ((ProEt.topology X).over W)
  intro V
  have h := congrArg (fun f ↦ f.app V)
    ((Over.forget W).toSheafify_pullbackSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology X).over W) (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))))
  change _ ≫ (e₀.hom.hom.app V ≫ c.hom.app V) =
    _ ≫ (e₀.hom.hom.app V ≫ e.hom.hom.app V)
  rw [← Category.assoc, ← Category.assoc]
  change _ ≫ e₀.hom.hom.app V = _ at h
  erw [h]
  exact (hc V.unop).trans (sfCbcConstantSliceIso_unit X W A V.unop).symm

attribute [local irreducible] sfCbcConstantSliceIso constantSheaf

/-- The canonical constant coefficient map, fixed by sheafification's unit. -/
def sfCbcConstantSliceMap (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] :=
  (sfCbcConstantSliceMap_existsUnique X W A).exists.choose

/-- Regard modules on the open scheme as modules on the ambient localized site. -/
def sfCbcConstantModuleToSlice (X : Scheme.{t}) (W : X.ProEt)
    (A : Type t) [CommRing A] :
    SheafOfModules.{t + 1} (adicModuleRing W.left A) ⥤
      SheafOfModules.{t + 1} ((adicModuleRing X A).over W) :=
  SheafOfModules.pushforward.{t + 1} (F := cbcSliceFunctor X W)
    (J := (ProEt.topology X).over W) (K := ProEt.topology W.left)
    ((sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (sfCbcConstantSliceMap X W A))

/-- Ordinary extension by zero of constant-coefficient module sheaves, for arbitrary A.
It is the direct-sum extension presheaf followed by module sheafification. -/
def sfCbcOpenExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    SheafOfModules.{t + 1} (adicModuleRing U A) ⥤
      SheafOfModules.{t + 1} (adicModuleRing X A) :=
  sfCbcConstantModuleToSlice X (cbcOpenObject j inferInstance) A ⋙
    SheafOfModules.localizedModuleExtension (adicConstantRing X A)
      (cbcOpenObject j inferInstance)

private theorem sfCbcModuleTransport
    {C D : Type (t + 1)} [Category.{t} C] [Category.{t} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.inverse.IsContinuous K J] [e.functor.IsContinuous J K]
    (R : Sheaf J RingCat.{t + 1}) (S : Sheaf K RingCat.{t + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{t + 1} K J).obj R) :
    (SheafOfModules.pushforward.{t + 1} (F := e.inverse) c.hom).IsEquivalence := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{t + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact inferInstanceAs
    (SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂).functor.IsEquivalence

/-- The constant coefficient extension is additive and exact. -/
theorem sfCbcOpenExtension_exact {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcOpenExtension j A).Additive ∧
      PreservesFiniteLimits (sfCbcOpenExtension j A) ∧
      PreservesFiniteColimits (sfCbcOpenExtension j A) := by
  let W := cbcOpenObject j inferInstance
  have hm : sfCbcConstantSliceMap X W A = (sfCbcConstantSliceIso X W A).hom := by
    unfold sfCbcConstantSliceMap
    exact (sfCbcConstantSliceMap_existsUnique X W A).unique
      (sfCbcConstantSliceMap_existsUnique X W A).exists.choose_spec
      (sfCbcConstantSliceIso_unit X W A)
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
  let c : ((adicModuleRing X A).over W) ≅
      ((cbcSliceFunctor X W).sheafPushforwardContinuous RingCat.{t + 1}
        ((ProEt.topology X).over W) (ProEt.topology W.left)).obj
          (adicModuleRing W.left A) := (sheafCompose ((ProEt.topology X).over W)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso (sfCbcConstantSliceIso X W A)
  have hF : (sfCbcConstantModuleToSlice X W A).IsEquivalence := by
    unfold sfCbcConstantModuleToSlice
    rw [hm]
    exact sfCbcModuleTransport ((ProEt.topology W.left)) ((ProEt.topology X).over W)
      (ProEt.sliceEquiv X W).symm (adicModuleRing W.left A)
      ((adicModuleRing X A).over W) c
  let := hF
  have : (sfCbcConstantModuleToSlice X W A).Additive :=
    ⟨fun {_ _} {_ _} ↦ by rfl⟩
  have : (SheafOfModules.localizedModuleExtension (adicConstantRing X A) W).Additive :=
    (SheafOfModules.localizedModuleExactIndependent.{t}
      (adicConstantRing X A) W).1
  have : PreservesFiniteLimits
      (SheafOfModules.localizedModuleExtension (adicConstantRing X A) W) :=
    (SheafOfModules.localizedModuleExactIndependent.{t}
      (adicConstantRing X A) W).2.1
  have : PreservesFiniteColimits
      (SheafOfModules.localizedModuleExtension (adicConstantRing X A) W) :=
    (SheafOfModules.localizedModuleExactIndependent.{t}
      (adicConstantRing X A) W).2.2.1
  change (sfCbcConstantModuleToSlice X W A ⋙
    SheafOfModules.localizedModuleExtension (adicConstantRing X A) W).Additive ∧
      PreservesFiniteLimits (sfCbcConstantModuleToSlice X W A ⋙
        SheafOfModules.localizedModuleExtension (adicConstantRing X A) W) ∧
      PreservesFiniteColimits (sfCbcConstantModuleToSlice X W A ⋙
        SheafOfModules.localizedModuleExtension (adicConstantRing X A) W)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity supplied by localized extension's exactness. -/
instance sfCbcOpenExtension_additive {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcOpenExtension j A).Additive := (sfCbcOpenExtension_exact j A).1

/-- Left exactness supplied by localized extension. -/
instance sfCbcOpenExtension_limits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteLimits (sfCbcOpenExtension j A) := (sfCbcOpenExtension_exact j A).2.1

/-- Right exactness supplied by localized extension. -/
instance sfCbcOpenExtension_colimits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteColimits (sfCbcOpenExtension j A) := (sfCbcOpenExtension_exact j A).2.2

/-- The ordinary uncompleted derived extension functor. -/
abbrev sfCbcDerivedExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    proEtaleDerivedCategory U A ⥤ proEtaleDerivedCategory X A :=
  (sfCbcOpenExtension j A).mapDerivedCategory

/-- Constant coefficients on the small model of the pro-etale site. -/
abbrev sfCbcModelRing (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  ConstantCompletion.constant (proEtaleModelTopology X) (ULift.{t + 1, t} A)

attribute [local semireducible] constantSheaf

/-- The coefficient transport is fixed on constant sections. -/
theorem sfCbcModelRingMap_existsUnique (X : Scheme.{t}) (A : Type t) [CommRing A] :
    ∃! c : sfCbcModelRing X A ⟶
      ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        CommRingCat.{t + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
          (adicConstantRing X A),
      IsIso c ∧ ∀ V : proEtaleSiteModel X,
        (toSheafify (proEtaleModelTopology X)
          ((Functor.const (proEtaleSiteModel X)ᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app (op V) ≫ c.hom.app (op V) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))).app (op (AsSmall.down.obj V)) := by
  let : HasWeakSheafify (ProEt.topology X) CommRingCat.{t + 1} := sfCbcWeakSheafifyProEt X
  let : HasWeakSheafify (proEtaleModelTopology X) CommRingCat.{t + 1} := sfCbcWeakSheafifyModel X
  let G : proEtaleSiteModel X ⥤ X.ProEt := AsSmall.down
  have : G.IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := X.ProEt)).inverse.IsEquivalence
  have : G.IsDenseSubsite (proEtaleModelTopology X) (ProEt.topology X) :=
    inferInstanceAs (AsSmall.down.IsDenseSubsite
      (AsSmall.down.inducedTopology (ProEt.topology X)) (ProEt.topology X))
  let P := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, t} A))
  let e := (G.pushforwardContinuousSheafificationCompatibility CommRingCat.{t + 1}
    (proEtaleModelTopology X) (ProEt.topology X)).app P
  have he (V : proEtaleSiteModel X) := congrArg (fun f ↦ f.app (op V))
    (G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{t + 1}
      (proEtaleModelTopology X) (ProEt.topology X) P)
  refine ⟨e.hom, ⟨inferInstance, he⟩, ?_⟩
  intro c hc
  apply sfCbcSheafifyHomExt (proEtaleModelTopology X)
  intro V
  exact (hc.2 V.unop).trans (he V.unop).symm

attribute [local irreducible] constantSheaf

/-- Canonical map from the small model's constant ring to the transported ring. -/
def sfCbcModelRingMap (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  (sfCbcModelRingMap_existsUnique X A).exists.choose

/-- Exact small-model transport with the canonical constant scalar action. -/
def sfCbcModelModules (X : Scheme.{t}) (A : Type t) [CommRing A] :
    SheafOfModules.{t + 1} (adicModuleRing X A) ⥤
      ConstantCompletion.Mod (sfCbcModelRing X A) :=
  proEtaleModuleToModel (adicModuleRing X A) ⋙
    ConstantCompletion.res (sfCbcModelRingMap X A)

private theorem sfCbcToModel_isEquivalence (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) :
    (proEtaleModuleToModel R).IsEquivalence := by
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{t + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj R
  have : (AsSmall.equiv.{t, t + 1, t + 1} (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  have : (AsSmall.equiv.{t, t + 1, t + 1} (C := X.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology X) (ProEt.topology X) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology X) (ProEt.topology X)
    infer_instance
  let e := SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{t, t + 1, t + 1} (C := X.ProEt)) (𝟙 R) (𝟙 S)
    (by ext V; dsimp [AsSmall.equiv]; erw [S.obj.map_id]; rfl)
    (by ext V; dsimp [AsSmall.equiv]; erw [R.obj.map_id]; rfl)
  exact inferInstanceAs e.inverse.IsEquivalence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem sfCbcRingIsoRestriction_isEquivalence
    {C : Type (t + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{t + 1}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{t + 1} c.hom).IsEquivalence := by
  let ec : C ≌ C := CategoryTheory.Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := SheafOfModules.pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [S.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : S ⟶ S ↦ (f.hom.app V).hom x) c.inv_hom_id.symm)
    (by
      ext V x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      simpa only [R.obj.map_id, ObjectProperty.FullSubcategory.id_hom,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.id_app, NatTrans.comp_app,
        RingCat.hom_id, RingCat.hom_comp, RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun f : R ⟶ R ↦ (f.hom.app V).hom x) c.hom_inv_id)
  exact inferInstanceAs e.functor.IsEquivalence

/-- Small-model transport is an additive equivalence. -/
theorem sfCbcModelModules_properties (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).IsEquivalence ∧ (sfCbcModelModules X A).Additive := by
  have h := (sfCbcModelRingMap_existsUnique X A).exists.choose_spec.1
  let : IsIso (sfCbcModelRingMap X A) := h
  let := sfCbcToModel_isEquivalence X (adicModuleRing X A)
  let c := (sheafCompose (proEtaleModelTopology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso
      (asIso (sfCbcModelRingMap X A))
  have : (ConstantCompletion.res (sfCbcModelRingMap X A)).IsEquivalence :=
    sfCbcRingIsoRestriction_isEquivalence c
  have : (proEtaleModuleToModel (adicModuleRing X A)).Additive :=
    ⟨fun {_ _} {_ _} ↦ by rfl⟩
  constructor
  · exact inferInstanceAs (proEtaleModuleToModel (adicModuleRing X A) ⋙
      ConstantCompletion.res (sfCbcModelRingMap X A)).IsEquivalence
  · exact inferInstanceAs (proEtaleModuleToModel (adicModuleRing X A) ⋙
      ConstantCompletion.res (sfCbcModelRingMap X A)).Additive

attribute [local irreducible] sfCbcModelModules sfCbcModelRingMap
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory

/-- The canonical model transport is an equivalence. -/
instance sfCbcModelModules_isEquivalence (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).IsEquivalence := (sfCbcModelModules_properties X A).1

/-- The canonical model transport preserves addition. -/
instance sfCbcModelModules_additive (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).Additive := (sfCbcModelModules_properties X A).2

private theorem sfCbcEquivalenceAdditive {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.IsEquivalence] [F.Additive] :
    F.asEquivalence.functor.Additive :=
  inferInstanceAs F.Additive

private theorem sfCbcInverseCompositeAdditive
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive B]
    (F : C ⥤ D) [F.IsEquivalence] [F.Additive]
    (G : C ⥤ E) [G.Additive] (H : E ⥤ B) [H.Additive] :
    (F.asEquivalence.inverse ⋙ G ⋙ H).Additive := by
  let : F.asEquivalence.functor.Additive := sfCbcEquivalenceAdditive F
  let : F.asEquivalence.inverse.Additive :=
    CategoryTheory.Equivalence.inverse_additive F.asEquivalence
  infer_instance

/-- Additivity of the forward equivalence in its bundled presentation. -/
instance sfCbcModelEquivalence_additive (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (sfCbcModelModules X A).asEquivalence.functor.Additive :=
  sfCbcEquivalenceAdditive (sfCbcModelModules X A)

/-- Standard localization size on the equivalent small site. -/
instance sfCbcModelModules_derived (X : Scheme.{t}) (A : Type t) [CommRing A] :
    HasDerivedCategory (ConstantCompletion.Mod (sfCbcModelRing X A)) :=
  HasDerivedCategory.standard _

/-- Standard localization size for strict towers. -/
instance sfCbcModelTowers_derived (X : Scheme.{t}) (A : Type t) [CommRing A] :
    HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod (sfCbcModelRing X A)) :=
  HasDerivedCategory.standard _

/-- The ordinary derived equivalence to the small model. -/
def sfCbcModelDerived (X : Scheme.{t}) (A : Type t) [CommRing A] :
    proEtaleDerivedCategory X A ≌ ConstantCompletion.D (sfCbcModelRing X A) :=
  (sfCbcModelModules X A).asEquivalence.mapDerivedCategory

/-- The standard factorization, expressed with the model equivalence. -/
def sfCbcModelDerivedFactors (X : Scheme.{t}) (A : Type t) [CommRing A] :
    adicLocalization X A ⋙ (sfCbcModelDerived X A).functor ≅
      (sfCbcModelModules X A).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.Q (sfCbcModelRing X A) :=
  (sfCbcModelModules X A).mapDerivedCategoryFactors

attribute [local irreducible] sfCbcModelDerived

/-- The ideal in the same lifted coefficient ring used by constant sheaves. -/
abbrev sfCbcModelIdeal {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    Ideal (ULift.{t + 1, t} A) := d.ideal.map ULift.ringEquiv.symm.toRingHom

/-- The derived category of actual strict towers in the small-site presentation. -/
abbrev sfCbcTowerDerived (X : Scheme.{t}) (A : Type t) [CommRing A] :=
  ConstantCompletion.TD (sfCbcModelRing X A)

attribute [local irreducible] SheafOfModules.monoidalCategory

section TensorTransport

set_option backward.isDefEq.respectTransparency true

private instance sfCbcTensorTotal {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [(MonoidalCategory.curriedTensor C).PreservesZeroMorphisms]
    [∀ M, ((MonoidalCategory.curriedTensor C).obj M).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} C] (P Q : CochainComplex C ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (MonoidalCategory.curriedTensor C) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (inferInstance : HasColimitsOfSize.{0, 0} C) _ _) _

private theorem sfCbcTensorComplexTransport
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D]
    [(MonoidalCategory.curriedTensor C).PreservesZeroMorphisms]
    [∀ M, ((MonoidalCategory.curriedTensor C).obj M).PreservesZeroMorphisms]
    [(MonoidalCategory.curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((MonoidalCategory.curriedTensor D).obj M).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    (P Q : CochainComplex C ℤ) :
    Nonempty ((F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor C)) ≅
        CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) (MonoidalCategory.curriedTensor D)) := by
  let τ : (Functor.postcompose₂.obj F).obj (MonoidalCategory.curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (MonoidalCategory.curriedTensor D) :=
    { app := fun X ↦
        { app := fun Y ↦ e.hom.app (X, Y)
          naturality := by
            intro Y Y' g
            simpa using e.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g) }
      naturality := by
        intro X X' f
        ext Y
        simpa using e.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y) }
  have (X Y : C) : IsIso ((τ.app X).app Y) := (e.app (X, Y)).isIso_hom
  exact ⟨asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q)⟩

private theorem sfCbcAcyclicTransport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] (P : CochainComplex C ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj P).Acyclic ↔ P.Acyclic := by
  constructor
  · intro h i
    exact (P.sc i).exact_map_iff_of_faithful F |>.1 (h i)
  · intro h i
    exact (P.sc i).exact_map_iff_of_faithful F |>.2 (h i)

private theorem sfCbcKFlatTransport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [(MonoidalCategory.curriedTensor C).PreservesZeroMorphisms]
    [∀ M, ((MonoidalCategory.curriedTensor C).obj M).PreservesZeroMorphisms]
    [(MonoidalCategory.curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((MonoidalCategory.curriedTensor D).obj M).PreservesZeroMorphisms]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    (P : CochainComplex C ℤ)
    (hP : ∀ Z : CochainComplex C ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z P (MonoidalCategory.curriedTensor C)).Acyclic) :
    ∀ Z : CochainComplex D ℤ, Z.Acyclic →
      (CochainComplex.mapBifunctor Z ((F.mapHomologicalComplex (.up ℤ)).obj P)
        (MonoidalCategory.curriedTensor D)).Acyclic := by
  let W := F.mapHomologicalComplex (.up ℤ)
  have : W.IsEquivalence :=
    (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  intro Z hZ
  let Z' := W.asEquivalence.inverse.obj Z
  have hZ' : Z'.Acyclic := (sfCbcAcyclicTransport F Z').mp
    (fun i ↦ (hZ i).of_iso (W.asEquivalence.counitIso.app Z).symm)
  obtain ⟨q⟩ := sfCbcTensorComplexTransport F e Z' P
  have hq : (CochainComplex.mapBifunctor (W.obj Z') (W.obj P)
      (MonoidalCategory.curriedTensor D)).Acyclic :=
    fun i ↦ ((sfCbcAcyclicTransport F _).mpr (hP Z' hZ') i).of_iso q
  let T := (MonoidalCategory.curriedTensor D).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)
  exact fun i ↦ (hq i).of_iso
    ((Functor.mapIso T (W.asEquivalence.counitIso.app Z)).app (W.obj P))

attribute [-instance] sfCbcTensorTotal

private theorem sfCbcFlatTransport
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.IsEquivalence]
    (e : MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    (P : C) (hP : exactFunctor C C (MonoidalCategory.tensorRight P)) :
    exactFunctor D D (MonoidalCategory.tensorRight (F.obj P)) := by
  let : PreservesFiniteLimits (MonoidalCategory.tensorRight P) := hP.1
  let : PreservesFiniteColimits (MonoidalCategory.tensorRight P) := hP.2
  let E := F.asEquivalence
  let q : MonoidalCategory.tensorRight P ⋙ F ≅
      F ⋙ MonoidalCategory.tensorRight (F.obj P) :=
    NatIso.ofComponents (fun M ↦ e.app (M, P)) (by
      intro M N f
      simpa using e.hom.naturality (X := (M, P)) (Y := (N, P)) (f, 𝟙 P))
  let c : E.inverse ⋙ MonoidalCategory.tensorRight P ⋙ F ≅
      MonoidalCategory.tensorRight (F.obj P) :=
    isoWhiskerLeft E.inverse q ≪≫
      isoWhiskerRight E.counitIso (MonoidalCategory.tensorRight (F.obj P))
  have : PreservesFiniteLimits (E.inverse ⋙ MonoidalCategory.tensorRight P ⋙ F) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (E.inverse ⋙ MonoidalCategory.tensorRight P ⋙ F) :=
    comp_preservesFiniteColimits _ _
  exact ⟨preservesFiniteLimits_of_natIso c, preservesFiniteColimits_of_natIso c⟩

private instance sfCbcSliceTransport_additive
    (X : Scheme.{t}) (W : X.ProEt) (A : Type t) [CommRing A] :
    (sfCbcConstantModuleToSlice X W A).Additive :=
  ⟨fun {_ _} {_ _} ↦ by rfl⟩

attribute [local irreducible] sfCbcConstantModuleToSlice

private theorem sfCbcSliceTransportKFlat
    (X : Scheme.{t}) (W : X.ProEt) (A : Type t) [CommRing A]
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing W.left A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing W.left A) P)
    (hflat : ∀ i : ℤ, CategoryTheory.exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (adicConstantRing W.left A)) (P.X i))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := (adicConstantRing X A).over W)
      (((sfCbcConstantModuleToSlice X W A).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
        (R := (adicConstantRing X A).over W)
        ((((sfCbcConstantModuleToSlice X W A).mapHomologicalComplex (.up ℤ)).obj P).X i) := by
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
  let R := adicConstantRing W.left A
  let S := (adicConstantRing X A).over W
  let c := sfCbcConstantSliceIso X W A
  let F := SheafOfModules.pushforward.{t + 1} (F := cbcSliceFunctor X W)
    (J := (ProEt.topology X).over W) (K := ProEt.topology W.left)
    (R := (sheafCompose (ProEt.topology W.left)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
    (S := (sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)
    ((sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map c.hom)
  have hFE : F.IsEquivalence := sfCbcModuleTransport (ProEt.topology W.left)
    ((ProEt.topology X).over W) (ProEt.sliceEquiv X W).symm (adicModuleRing W.left A)
    ((adicModuleRing X A).over W)
    ((sheafCompose ((ProEt.topology X).over W)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso c)
  have hF : sfCbcConstantModuleToSlice X W A = F := by
    have hm : sfCbcConstantSliceMap X W A = c.hom := by
      unfold sfCbcConstantSliceMap
      exact (sfCbcConstantSliceMap_existsUnique X W A).unique
        (sfCbcConstantSliceMap_existsUnique X W A).exists.choose_spec
        (sfCbcConstantSliceIso_unit X W A)
    unfold sfCbcConstantModuleToSlice
    rw [hm]
    rfl
  have : (sfCbcConstantModuleToSlice X W A).IsEquivalence := by
    rw [hF]
    exact hFE
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let : MonoidalCategory (SheafOfModules.{t + 1} ((adicModuleRing X A).over W)) :=
    SheafOfModules.monoidalCategory S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  let : (MonoidalCategory.curriedTensor
      (SheafOfModules.{t + 1} ((adicModuleRing X A).over W))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let : ∀ N : SheafOfModules.{t + 1} ((adicModuleRing X A).over W),
      ((MonoidalCategory.curriedTensor _).obj N).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  obtain ⟨q⟩ := SheafOfModules.pushforward_equivalence_tensor_iso
    ((ProEt.topology X).over W) (ProEt.topology W.left) (ProEt.sliceEquiv X W) R S c
  have q' : MonoidalCategory.tensor _ ⋙ sfCbcConstantModuleToSlice X W A ≅
      (sfCbcConstantModuleToSlice X W A).prod (sfCbcConstantModuleToSlice X W A) ⋙
        MonoidalCategory.tensor _ := by
    rw [hF]
    exact q
  refine ⟨sfCbcKFlatTransport (sfCbcConstantModuleToSlice X W A) q' P hP, ?_⟩
  intro i
  have hi := sfCbcFlatTransport (sfCbcConstantModuleToSlice X W A) q' (P.X i) (hflat i)
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S
      ((sfCbcConstantModuleToSlice X W A).obj (P.X i))).symm hi

-- Compare the two complex constructions before substituting concrete module functors.
private theorem sfCbcMapComplexCompProp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [_hF : F.Additive] [_hG : G.Additive]
    (P : CochainComplex C ℤ) (Q : CochainComplex E ℤ → Prop)
    (h : Q ((G.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P))) :
    Q (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj P) := h

private theorem sfCbcKFlatModel_ext (X : Scheme.{t}) (A : Type t) [CommRing A]
    {K : proEtaleDerivedCategory X A} (M N : AdicKFlatModel X A K)
    (hc : M.complex = N.complex) (he : HEq M.realization N.realization) : M = N := by
  rcases M with ⟨C, hC, hf, e⟩
  rcases N with ⟨C', hC', hf', e'⟩
  dsimp only at hc
  subst C'
  have h : e = e' := eq_of_heq he
  cases h
  rfl

private theorem sfCbcSpecifiedModel_existsUnique (X : Scheme.{t})
    (A : Type t) [CommRing A] {K : proEtaleDerivedCategory X A}
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X A)) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A) C)
    (hCf : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (adicConstantRing X A)) (C.X i)))
    (e : (adicLocalization X A).obj C ≅ K) :
    ∃! N : AdicKFlatModel X A K, N.complex = C ∧ HEq N.realization e := by
  let N : AdicKFlatModel X A K := ⟨C, hC, hCf, e⟩
  refine ⟨N, ⟨rfl, HEq.rfl⟩, ?_⟩
  intro N' hN'
  exact sfCbcKFlatModel_ext X A N' N hN'.1 hN'.2

/-- The flat K-flat model of extension is the actual termwise extended complex. -/
theorem sfCbcExtensionModel_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A]
    {K : proEtaleDerivedCategory U A} (M : AdicKFlatModel U A K) :
    ∃! N : AdicKFlatModel X A ((sfCbcDerivedExtension j A).obj K),
      N.complex = ((sfCbcOpenExtension j A).mapHomologicalComplex (.up ℤ)).obj M.complex ∧
      HEq N.realization
        (((sfCbcOpenExtension j A).mapDerivedCategoryFactors.app M.complex).symm ≪≫
          (sfCbcDerivedExtension j A).mapIso M.realization) := by
  let W := cbcOpenObject j inferInstance
  let F : SheafOfModules.{t + 1} (adicModuleRing U A) ⥤
      SheafOfModules.{t + 1} ((adicModuleRing X A).over W) :=
    sfCbcConstantModuleToSlice X W A
  let G : SheafOfModules.{t + 1} ((adicModuleRing X A).over W) ⥤
      SheafOfModules.{t + 1} (adicModuleRing X A) :=
    SheafOfModules.localizedModuleExtension.{t} (adicConstantRing X A) W
  have hF : F.Additive := sfCbcSliceTransport_additive X W A
  have hG : G.Additive := SheafOfModules.localizedModuleExtension_additive
    (adicConstantRing X A) W
  let P := (F.mapHomologicalComplex (.up ℤ)).obj M.complex
  obtain ⟨hP, hflat⟩ := sfCbcSliceTransportKFlat X W A M.complex M.isKFlat M.flatTerms
  obtain ⟨hk, hf, _⟩ := SheafOfModules.ringedOpen_preserves_flat_resolution.{t + 1, t, t + 1}
    (adicConstantRing X A) W
  let C := ((sfCbcOpenExtension j A).mapHomologicalComplex (.up ℤ)).obj M.complex
  have hC : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A) C :=
    sfCbcMapComplexCompProp F G (_hF := hF) (_hG := hG) M.complex
      (fun T ↦ CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X A) T)
      (hk P hP)
  have hCf (i : ℤ) : CategoryTheory.exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (adicConstantRing X A)) (C.X i)) := by
    apply sfCbcMapComplexCompProp F G (_hF := hF) (_hG := hG) M.complex
      (fun T ↦ CategoryTheory.exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (adicConstantRing X A)) (T.X i)))
    let T := (G.mapHomologicalComplex (.up ℤ)).obj P
    exact (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (adicConstantRing X A) (T.X i)) (hf P hflat i)
  exact sfCbcSpecifiedModel_existsUnique X A C hC hCf
    (((sfCbcOpenExtension j A).mapDerivedCategoryFactors.app M.complex).symm ≪≫
      (sfCbcDerivedExtension j A).mapIso M.realization)

attribute [-instance] sfCbcSliceTransport_additive

end TensorTransport

attribute [local irreducible] sfCbcOpenExtension

/-- The canonical termwise extended model; its complex and realization determine it. -/
def sfCbcExtensionModel {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] {K : proEtaleDerivedCategory U A}
    (M : AdicKFlatModel U A K) :=
  (sfCbcExtensionModel_existsUnique j A M).exists.choose

attribute [local irreducible] sfCbcExtensionModel

/-- Ordinary extension transported to the equivalent small-site module categories. -/
def sfCbcModelExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    ConstantCompletion.Mod (sfCbcModelRing U A) ⥤
      ConstantCompletion.Mod (sfCbcModelRing X A) :=
  (sfCbcModelModules U A).asEquivalence.inverse ⋙ sfCbcOpenExtension j A ⋙
    sfCbcModelModules X A

/-- Additivity is preserved through the two model equivalences. -/
instance sfCbcModelExtension_additive {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcModelExtension j A).Additive :=
  sfCbcInverseCompositeAdditive (sfCbcModelModules U A)
    (sfCbcOpenExtension j A) (sfCbcModelModules X A)

/-- Left exactness survives the equivalence transport. -/
instance sfCbcModelExtension_limits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteLimits (sfCbcModelExtension j A) :=
  inferInstanceAs (PreservesFiniteLimits ((sfCbcModelModules U A).asEquivalence.inverse ⋙
    sfCbcOpenExtension j A ⋙ sfCbcModelModules X A))

/-- Right exactness survives the equivalence transport. -/
instance sfCbcModelExtension_colimits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteColimits (sfCbcModelExtension j A) :=
  inferInstanceAs (PreservesFiniteColimits ((sfCbcModelModules U A).asEquivalence.inverse ⋙
    sfCbcOpenExtension j A ⋙ sfCbcModelModules X A))

/-- Exact termwise extension on the derived small-site presentation. -/
abbrev sfCbcModelDerivedExtension {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :=
  (sfCbcModelExtension j A).mapDerivedCategory

/-- The standard factorization for model extension, with its named derived functor. -/
def sfCbcModelExtensionFactors {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    ConstantCompletion.Q (sfCbcModelRing U A) ⋙ sfCbcModelDerivedExtension j A ≅
      (sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.Q (sfCbcModelRing X A) :=
  (sfCbcModelExtension j A).mapDerivedCategoryFactors

/-- The termwise ordinary extension functor on actual strict towers. -/
abbrev sfCbcTowerExtension {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (sfCbcModelExtension j A)

private theorem sfCbcWhiskeringRightExact {C D I : Type*}
    [Category C] [Category D] [Category I] [Preadditive C] [Preadditive D]
    [HasFiniteLimits C] [HasFiniteColimits C] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ((Functor.whiskeringRight I C D).obj F).Additive ∧
      PreservesFiniteLimits ((Functor.whiskeringRight I C D).obj F) ∧
      PreservesFiniteColimits ((Functor.whiskeringRight I C D).obj F) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Termwise extension is exact also on strict towers. -/
theorem sfCbcTowerExtension_exact {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcTowerExtension j A).Additive ∧
      PreservesFiniteLimits (sfCbcTowerExtension j A) ∧
      PreservesFiniteColimits (sfCbcTowerExtension j A) := by
  exact sfCbcWhiskeringRightExact (I := ℕᵒᵖ) (sfCbcModelExtension j A)

/-- Additivity of termwise extension. -/
instance sfCbcTowerExtension_additive {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    (sfCbcTowerExtension j A).Additive := (sfCbcTowerExtension_exact j A).1

/-- Left exactness of termwise extension. -/
instance sfCbcTowerExtension_limits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteLimits (sfCbcTowerExtension j A) := (sfCbcTowerExtension_exact j A).2.1

/-- Right exactness of termwise extension. -/
instance sfCbcTowerExtension_colimits {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    PreservesFiniteColimits (sfCbcTowerExtension j A) := (sfCbcTowerExtension_exact j A).2.2

/-- The ordinary exact extension functor on derived strict towers. -/
abbrev sfCbcDerivedTowerExtension {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type t) [CommRing A] :
    sfCbcTowerDerived U A ⥤ sfCbcTowerDerived X A :=
  (sfCbcTowerExtension j A).mapDerivedCategory

/-- The standard factorization for strict tower extension with named endpoints. -/
def sfCbcTowerExtensionFactors {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    ConstantCompletion.TQ (sfCbcModelRing U A) ⋙ sfCbcDerivedTowerExtension j A ≅
      (sfCbcTowerExtension j A).mapHomologicalComplex (.up ℤ) ⋙
        ConstantCompletion.TQ (sfCbcModelRing X A) :=
  (sfCbcTowerExtension j A).mapDerivedCategoryFactors

/-- The universal K-flat presentation of strict reductions on the small model. -/
abbrev sfCbcQuotientPresentation (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) :=
  ConstantCompletion.quotientPresentation (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false

end AlgebraicGeometry.Scheme
