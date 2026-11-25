/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit

/-! # Generic completed unit transport through a realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u a v w wc
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  purZlReduction sfbConstantRingAbIso
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

section RealizationSingleSquare
variable {A B C D : Type a}
  [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
  {F : A ⥤ B} {G : C ⥤ D} [F.Additive] [G.Additive]
  (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
  (ordinary : F ⋙ V ≅ U ⋙ G)

private theorem realization_singleFactor (M : A) :
    (U.mapDerivedCategorySingleFunctor 0).hom.app M =
      U.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) := by
  exact (Iso.inv_comp_eq (U.mapDerivedCategoryFactors.app _)).mp
    (U.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M)

/-- The full derived-unit square evaluated on a single coefficient object.
Source: diagonal trace universal-unit normalization.
(blueprint: def-diagonal-coefficient-unit-push).
Proof: evaluate the normalization on the single complex and cancel the canonical
single-complex comparisons. Their coherence is checked in each degree. -/
private theorem realization_single_square
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary) (M : A) :
    V.mapDerivedCategory.map (singlePushComparison RF M) ≫
        s.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) =
      (V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) ≫
          singlePushComparison RG (U.obj M) := by
  let P := (HomologicalComplex.single A (.up ℤ) 0).obj M
  have hn := s.normalization P
  unfold singlePushComparison
  rw [realization_singleFactor U M, RG.R.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  have hη := RG.η.naturality
    ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)
  change DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)) ≫
      RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M)) =
    RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫ RG.R.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M)) at hη
  erw [← hη]
  have hV := V.mapDerivedCategoryFactors.hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  change V.mapDerivedCategory.map
      (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) ≫
      V.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    V.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫
      DerivedCategory.Q.map ((V.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)) at hV
  erw [reassoc_of% hV]
  rw [realization_singleFactor V (F.obj M)]
  have hc :
      (V.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app P ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app M) =
      (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).hom.app (F.obj M) ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (ordinary.hom.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app (U.obj M) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f]
      dsimp [P, HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
      change V.map (𝟙 (F.obj M)) ≫ ordinary.hom.app M ≫
        G.map (𝟙 (U.obj M)) =
          (𝟙 (V.obj (F.obj M))) ≫
            ((𝟙 (V.obj (F.obj M))) ≫ ordinary.hom.app M ≫ (𝟙 _)) ≫ (𝟙 _)
      simp only [Category.id_comp, Category.comp_id]
      exact (congrArg₂ (fun k h => k ≫ ordinary.hom.app M ≫ h)
        (V.map_id (F.obj M)) (G.map_id (U.obj M))).trans
          ((Category.id_comp _).trans (Category.comp_id _))
    · simp [P, HomologicalComplex.singleMapHomologicalComplex,
        HomologicalComplex.single, hn]
  have hs : (DerivedCategory.singleFunctor D 0).map (ordinary.hom.app M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single D (.up ℤ) 0).map (ordinary.hom.app M)) := rfl
  rw [hs]
  have hq := congrArg DerivedCategory.Q.map hc
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k => V.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj M)) ≫ k ≫
        RG.η.app ((HomologicalComplex.single C (.up ℤ) 0).obj (U.obj M))) hq

private theorem realization_unit_square
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary)
    (NX : A) (NS : B) (MX : C) (MS : D)
    (iX : U.obj NX ≅ MX) (iS : V.obj NS ≅ MS)
    (m : NS ⟶ F.obj NX) (a : MS ⟶ G.obj MX)
    (hm : V.map m ≫ ordinary.hom.app NX ≫ G.map iX.hom = iS.hom ≫ a) :
    V.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor B 0).map m ≫ singlePushComparison RF NX) ≫
      s.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj NX) ≫
      RG.R.map ((U.mapDerivedCategorySingleFunctor 0).hom.app NX ≫
        (DerivedCategory.singleFunctor C 0).map iX.hom) =
    ((V.mapDerivedCategorySingleFunctor 0).hom.app NS ≫
      (DerivedCategory.singleFunctor D 0).map iS.hom) ≫
      (DerivedCategory.singleFunctor D 0).map a ≫ singlePushComparison RG MX := by
  have hs := realization_single_square U V RF RG ordinary s NX
  have hn := (V.mapDerivedCategorySingleFunctor 0).hom.naturality m
  change V.mapDerivedCategory.map ((DerivedCategory.singleFunctor B 0).map m) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app _ =
    (V.mapDerivedCategorySingleFunctor 0).hom.app NS ≫
      (DerivedCategory.singleFunctor D 0).map (V.map m) at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hs, reassoc_of% hn]
  erw [← singlePushComparison_naturality RG iX.hom]
  have hh := congrArg (DerivedCategory.singleFunctor D 0).map hm
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ (V.mapDerivedCategorySingleFunctor 0).hom.app NS ≫
      k ≫ singlePushComparison RG MX) hh

private theorem realization_unit_square_comp
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary)
    (NX : A) (NS : B) (MX : C) (MS : D)
    (iX : U.obj NX ≅ MX) (iS : V.obj NS ≅ MS)
    (m : NS ⟶ F.obj NX) (a : MS ⟶ G.obj MX)
    (hm : V.map m ≫ ordinary.hom.app NX ≫ G.map iX.hom = iS.hom ≫ a)
    (T : DerivedCategory C) (q : (DerivedCategory.singleFunctor C 0).obj MX ⟶ T) :
    V.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor B 0).map m ≫ singlePushComparison RF NX) ≫
      s.iso.hom.app ((DerivedCategory.singleFunctor A 0).obj NX) ≫
      RG.R.map (((U.mapDerivedCategorySingleFunctor 0).hom.app NX ≫
        (DerivedCategory.singleFunctor C 0).map iX.hom) ≫ q) =
    ((V.mapDerivedCategorySingleFunctor 0).hom.app NS ≫
      (DerivedCategory.singleFunctor D 0).map iS.hom) ≫
      ((DerivedCategory.singleFunctor D 0).map a ≫ singlePushComparison RG MX) ≫
        RG.R.map q := by
  have h := realization_unit_square U V RF RG ordinary s NX NS MX MS iX iS m a hm
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ RG.R.map q) h

end RealizationSingleSquare

-- The ordinary unit comparison uses concrete sheaf and module instances.
private theorem completed_ordinary_unit_general
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    (eS : CompletedRealization l S) (eX : CompletedRealization l X)
    (ordinary : diagonalTracePush l f ⋙ eS.F ≅
      eX.F ⋙ CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hordinary : ∀ M : DiagonalCompleted l X,
      HEq ((ordinary.hom.app M).hom ≫
        (lowerStar Ab.{u + 1} f).map (eX.underlying.hom.app M))
        (eS.underlying.hom.app ((diagonalTracePush l f).obj M))) :
    eS.F.map (DiagonalTrace.completedPushUnit l f) ≫ ordinary.hom.app _ ≫
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).map
          eX.unitIso.hom =
      eS.unitIso.hom ≫
        (CondensedRing.upperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).homEquiv _ _
          (Functor.Monoidal.εIso (CondensedRing.upperStar
            (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)).inv := by
  let UY := SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
  let UP := SheafOfModules.unit (Scheme.purTwistRing X
    (Scheme.purTwistZlCompletion X l))
  let G := lowerStar Ab.{u + 1} f
  let m := DiagonalTrace.completedPushUnit l f
  let a := (SheafOfModules.toSheaf
    (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))).map m
  have ho := eq_of_heq (hordinary UP)
  have hn := eS.underlying.hom.naturality m
  have h : (eS.F.map m).hom ≫ (ordinary.hom.app UP).hom =
      eS.underlying.hom.app UY ≫ a ≫ G.map (eX.underlying.inv.app UP) := by
    apply (cancel_mono (G.map (eX.underlying.hom.app UP))).mp
    simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_app,
      G.map_id]
    rw [ho]
    exact hn
  apply (cancel_epi eS.unitIso.inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply Mod.regular_hom_ext
  simp only [Mod.comp_hom', CondensedRing.lowerStar_map_hom]
  rw [reassoc_of% h]
  have hY := unitRealization_inv_one l S eS
  have hP := unitRealization_one l X eX
  change η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) S] ≫
    (eS.unitIso.inv.hom ≫ eS.underlying.hom.app UY) = _ at hY
  change η[(completedAbFunctor X).obj
      (Scheme.purTwistZlCompletion X l)] ≫
    (eX.underlying.inv.app UP ≫ eX.unitIso.hom.hom) = _ at hP
  erw [reassoc_of% hY]
  erw [reassoc_of% completedPushUnit_one l f]
  erw [CondensedRing.homEquiv_εIso_inv_hom]
  have hc := (isMonHom_condensedPushforwardHom
    (Profinite.continuousMapRingObj.{u} ℤ_[l]) f).one_hom
  erw [hc]
  change _ = Functor.LaxMonoidal.ε G ≫ G.map
    η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ Functor.LaxMonoidal.ε G ≫ G.map k) hP

-- Concrete coefficient instances are compared only at the generic lemma boundary.
/-- The realized completed unit transport, with an arbitrary local arrow.

Source: diagonal tower coefficient changes (1), exact completed push-square
normalization and the ordinary coefficient-unit normalization.
(blueprint: lem-diagonal-completed-realized-unit-transport).

Proof: evaluate the exact square on the single completed unit, use naturality
of the single comparison and of the realization's degree-zero comparison, then
apply the ordinary unit equation. The result is postcomposed with an arbitrary
local arrow, so this statement contains no Chern normalization.
-/
theorem diagonalCompletedRealizedUnitTransport (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (push : CompletedPushSquare l f eX eS R D)
    (T : DerivedCategory (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))
    (q : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶ T) :
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let UX := SheafOfModules.unit
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
    let m := DiagonalTrace.completedPushUnit l f
    let a := (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv
    let unitPush := (DerivedCategory.singleFunctor _ 0).map a ≫
      singlePushComparison D (Mod.regular (condensedRingObj Λ X))
    let b₀ := (DerivedCategory.singleFunctor _ 0).map m ≫
      singlePushComparison R UX
    eS.F.mapDerivedCategory.map b₀ ≫ push.derived.iso.hom.app
        (DiagonalTrace.completedUnit l X) ≫ D.R.map (eX.singleUnit l X ≫ q) =
      eS.singleUnit l S ≫ unitPush ≫ D.R.map q := by
  exact realization_unit_square_comp eX.F eS.F R D push.ordinary push.derived
    _ _ _ _ eX.unitIso eS.unitIso (DiagonalTrace.completedPushUnit l f) _
    (completed_ordinary_unit_general l f eS eX push.ordinary
      push.ordinary_normalization) T q

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
