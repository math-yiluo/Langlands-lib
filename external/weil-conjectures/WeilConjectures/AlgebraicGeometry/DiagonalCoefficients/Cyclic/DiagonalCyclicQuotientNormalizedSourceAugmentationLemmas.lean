/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientNormalizedSourceEndpointLemmas
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientProjection
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedIntegralGeneratorSections
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalOrdinarySourceNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientNormalizedSourceEndpointLemmas

/-! # Augmentation lemmas for the cyclic normalized source endpoint

The augmentation half of `DiagonalCyclicQuotientNormalizedSourceEndpointLemmas`, split off to
keep the time and memory needed to compile each module below the build limits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom
  isCommMonObj_condensedRingObj Profinite.isCommMonObj_continuousMapRingObj

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction

attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  cyclicLine cyclicLineMap derivedScalars
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local semireducible] diagonalForget diagonalFiniteToPadic
attribute [local semireducible] derivedScalars
set_option backward.defeqAttrib.useBackward true
attribute [local instance 5000] sheafMonoidalCategory sheafBraidedCategory

private theorem single_comparison_post
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : A) {N : B} (s : F.obj P ≅ N)
    {X Y : DerivedCategory C} {J : C}
    (d0 : X ⟶ Y) (d1 : Y ⟶ G.mapDerivedCategory.obj
      (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj P)))
    (j0 : X ⟶ (DerivedCategory.singleFunctor C 0).obj J) (j : J ⟶ G.obj (F.obj P))
    (h : d0 ≫ d1 ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app P) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj P) =
        j0 ≫ (DerivedCategory.singleFunctor C 0).map j) :
    d0 ≫ d1 ≫ G.mapDerivedCategory.map
      (((F.mapDerivedCategorySingleFunctor 0).app P ≪≫
        (DerivedCategory.singleFunctor B 0).mapIso s).hom) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app N =
    j0 ≫ (DerivedCategory.singleFunctor C 0).map (j ≫ G.map s.hom) := by
  have hn := (G.mapDerivedCategorySingleFunctor 0).hom.naturality s.hom
  dsimp only [Functor.comp_map] at hn
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  change d0 ≫ d1 ≫
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app P) ≫
    G.mapDerivedCategory.map ((DerivedCategory.singleFunctor B 0).map s.hom) ≫
    (G.mapDerivedCategorySingleFunctor 0).hom.app N = _
  rw [hn]
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ f ≫ (DerivedCategory.singleFunctor C 0).map (G.map s.hom)) h

private theorem augmentation_transport
    {A B : Type*} [Category A] [Category B] (S : A ⥤ B)
    {P₀ P₁ P₂ P₃ P₄ : A} (f0 : P₀ ⟶ P₁) (f1 : P₁ ⟶ P₂)
    (f2 : P₂ ⟶ P₃) (f3 : P₃ ⟶ P₄)
    {X B₀ C₀ C₁ D₀ D₁ D₂ E : B}
    (u : X ⟶ B₀) (d : B₀ ⟶ C₀) (a : C₀ ⟶ D₀) (e : E ≅ D₀)
    (q0 : C₀ ⟶ C₁) (q1 : D₀ ⟶ D₁) (a1 : C₁ ⟶ D₁)
    (d1 : D₁ ⟶ D₂) (c1 : D₂ ⟶ S.obj P₃) (r0 : C₁ ⟶ S.obj P₂)
    (j : X ⟶ S.obj P₀) (r : D₀ ⟶ D₂)
    (hr : r = q1 ≫ d1) (hn : a ≫ q1 = q0 ≫ a1)
    (hs : a1 ≫ d1 ≫ c1 = r0 ≫ S.map f2)
    (hb : u ≫ d ≫ q0 ≫ r0 = j ≫ S.map (f0 ≫ f1)) :
    u ≫ (d ≫ a ≫ e.inv) ≫ (e.hom ≫ r ≫ c1 ≫ S.map f3) =
      j ≫ S.map (f0 ≫ f1 ≫ f2 ≫ f3) := by
  rw [hr]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn, reassoc_of% hs]
  have h := congrArg (fun f ↦ f ≫ S.map f2 ≫ S.map f3) hb
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using h

private theorem cyclic_augmentation_forward
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (p : CyclicCartierFrame l Y n) :
    let U := diagonalForget l (diagonalSurface Y)
    let Z := diagonalCompletedRestriction l (diagonalSurface Y)
    let V := Mod.forget (D := DiagonalAb (diagonalSurface Y))
      (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) (diagonalSurface Y))
    let R := derivedScalars (cyclicMap l n) (diagonalSurface Y)
    let P := diagonalCompletedSource l Y
    let N := source (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) Y
    let q := (eW.F.mapDerivedCategorySingleFunctor 0).app P ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso sourceIso
    let m := p.eW.underlying.inv.app N ≫
      (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)).map
        p.sourceComparison.iso.hom
    let c := (cyclicEvaluationUnderlying l Y n eW p).hom.app
        (diagonalCompletedDomain l Y) ≫
      V.mapDerivedCategory.map (R.map q.hom ≫ p.supported.iso.hom) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor _ 0).map m
    U.mapDerivedCategory.map ((Z.mapDerivedCategorySingleFunctor 0).inv.app P) ≫
        (cyclicEvaluationAugmentation l Y n eW p).app
          (diagonalCompletedDomain l Y) ≫ c =
      (U.mapDerivedCategorySingleFunctor 0).hom.app (Z.obj P) ≫
        (DerivedCategory.singleFunctor _ 0).map
          (eW.underlying.inv.app P ≫ sourceIso.hom.hom ≫
            p.supported.semilinear.hom.hom ≫ m) := by
  dsimp only
  let U := diagonalForget l (diagonalSurface Y)
  let Z := diagonalCompletedRestriction l (diagonalSurface Y)
  let V := Mod.forget (D := DiagonalAb (diagonalSurface Y))
    (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) (diagonalSurface Y))
  let V0 := Mod.forget (D := DiagonalAb (diagonalSurface Y))
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (diagonalSurface Y))
  let R := derivedScalars (cyclicMap l n) (diagonalSurface Y)
  let P := diagonalCompletedSource l Y
  let q := (eW.F.mapDerivedCategorySingleFunctor 0).app P ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso sourceIso
  let N := source (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) Y
  let S := DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0
  let m := p.eW.underlying.inv.app N ≫
    (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)).map
      p.sourceComparison.iso.hom
  have hn := (scalarUnderlyingUnit (cyclicMap l n) (diagonalSurface Y)).naturality q.hom
  dsimp only [Functor.comp_map] at hn
  have hs := scalar_unit_endpoint (cyclicMap l n) (diagonalSurface Y) p.supported
  have hb := single_comparison_post eW.F V0 P sourceIso
    (U.mapDerivedCategory.map ((Z.mapDerivedCategorySingleFunctor 0).inv.app P))
    ((cyclicCompletedUnderlying l Y eW).hom.app (diagonalCompletedDomain l Y))
    ((U.mapDerivedCategorySingleFunctor 0).hom.app (Z.obj P))
    (eW.underlying.inv.app P) (completed_underlying_single l Y eW)
  exact augmentation_transport S (eW.underlying.inv.app P) sourceIso.hom.hom
    p.supported.semilinear.hom.hom m
    (U.mapDerivedCategory.map ((Z.mapDerivedCategorySingleFunctor 0).inv.app P))
    ((cyclicCompletedUnderlying l Y eW).hom.app (diagonalCompletedDomain l Y))
    ((scalarUnderlyingUnit (cyclicMap l n) (diagonalSurface Y)).app
      (eW.F.mapDerivedCategory.obj (diagonalCompletedDomain l Y)))
    ((cyclicEvaluationUnderlying l Y n eW p).app (diagonalCompletedDomain l Y))
    (V0.mapDerivedCategory.map q.hom) (V.mapDerivedCategory.map (R.map q.hom))
    ((scalarUnderlyingUnit (cyclicMap l n) (diagonalSurface Y)).app
      ((DerivedCategory.singleFunctor _ 0).obj
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)))
    (V.mapDerivedCategory.map p.supported.iso.hom)
    ((V.mapDerivedCategorySingleFunctor 0).hom.app N)
    ((V0.mapDerivedCategorySingleFunctor 0).hom.app
      (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y))
    ((U.mapDerivedCategorySingleFunctor 0).hom.app (Z.obj P))
    (V.mapDerivedCategory.map (R.map q.hom ≫ p.supported.iso.hom))
    (V.mapDerivedCategory.map_comp _ _) hn.symm hs hb

private theorem generator_augmentation
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {I : B} {P Q : A} {X E : DerivedCategory A}
    (t : X ≅ (DerivedCategory.singleFunctor A 0).obj P)
    (σ : (DerivedCategory.singleFunctor A 0).obj Q ⟶ E)
    (α : U.mapDerivedCategory.obj X ⟶ U.mapDerivedCategory.obj E)
    (c : U.mapDerivedCategory.obj E ≅
      (DerivedCategory.singleFunctor B 0).obj (U.obj Q))
    (γ : I ⟶ U.obj P) (g : I ⟶ U.obj Q) (m : U.obj P ⟶ U.obj Q)
    (hσ : U.mapDerivedCategory.map σ ≫ c.hom =
      (U.mapDerivedCategorySingleFunctor 0).hom.app Q)
    (hα : U.mapDerivedCategory.map t.inv ≫ α ≫ c.hom =
      (U.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        (DerivedCategory.singleFunctor B 0).map m)
    (hm : γ ≫ m = g) :
    ((DerivedCategory.singleFunctor B 0).map γ ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app P ≫
        U.mapDerivedCategory.map t.inv) ≫ α =
    (DerivedCategory.singleFunctor B 0).map g ≫
      (U.mapDerivedCategorySingleFunctor 0).inv.app Q ≫ U.mapDerivedCategory.map σ := by
  apply (cancel_mono c.hom).mp
  simp only [Category.assoc, hα, hσ, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, ← CategoryTheory.Functor.map_comp, hm]
  exact (Category.comp_id _).symm

private theorem normalized_inverse
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {P Q R T : A} {I : B} (γ : I ⟶ F.obj P) (π : P ⟶ Q)
    (a : I ⟶ F.obj R) (p : R ⟶ Q) (s : Q ≅ T)
    (g : I ⟶ F.obj T)
    (hπ : γ ≫ F.map π = a ≫ F.map p)
    (hs : a ≫ F.map (p ≫ s.hom) = g) :
    γ ≫ F.map π = g ≫ F.map s.inv := by
  rw [hπ, ← hs]
  simp only [Category.assoc, ← F.map_comp, s.hom_inv_id, Category.comp_id]

namespace CyclicAugmentation

theorem endpoint_generator_argument
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U.Faithful] {I : B} {P Q N : A} {X E F : DerivedCategory A}
    (t : X ≅ (DerivedCategory.singleFunctor A 0).obj P)
    (σ : (DerivedCategory.singleFunctor A 0).obj Q ⟶ E)
    (w : E ⟶ F) (r : F ⟶ (DerivedCategory.singleFunctor A 0).obj N)
    (α : U.mapDerivedCategory.obj X ⟶ U.mapDerivedCategory.obj E)
    (μ : X ⟶ F) (γ : I ⟶ U.obj P) (g : I ⟶ U.obj Q) [Epi g]
    (π : P ⟶ N) (s : Q ⟶ N)
    (hγ : ((DerivedCategory.singleFunctor B 0).map γ ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app P ≫
          U.mapDerivedCategory.map t.inv) ≫ α =
      (DerivedCategory.singleFunctor B 0).map g ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app Q ≫ U.mapDerivedCategory.map σ)
    (he : α ≫ U.mapDerivedCategory.map w = U.mapDerivedCategory.map μ)
    (hproject : μ ≫ r = t.hom ≫ (DerivedCategory.singleFunctor A 0).map π)
    (hordinary : γ ≫ U.map π = g ≫ U.map s) :
    σ ≫ w ≫ r = (DerivedCategory.singleFunctor A 0).map s := by
  apply single_generator_injective U g
  simp only [CategoryTheory.Functor.map_comp]
  rw [← reassoc_of% hγ]
  rw [reassoc_of% he, ← U.mapDerivedCategory.map_comp, hproject]
  simp only [CategoryTheory.Functor.map_comp,
    ← U.mapDerivedCategory.map_comp_assoc, t.inv_hom_id, U.mapDerivedCategory.map_id,
    Category.id_comp]
  have hπ := (U.mapDerivedCategorySingleFunctor 0).inv.naturality π
  have hs := (U.mapDerivedCategorySingleFunctor 0).inv.naturality s
  dsimp only [Functor.comp_map] at hπ hs
  rw [← hπ, ← hs]
  simp only [← CategoryTheory.Functor.map_comp_assoc, hordinary]

end CyclicAugmentation

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
