/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientNormalizedSourceEndpointLemmas
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientNormalizedSourceAugmentationLemmas
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

/-! # Quotient and normalized endpoint comparisons for cyclic coefficients -/

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

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Retain the named normalization hypotheses of the existing public interface.
set_option linter.unusedVariables false in
/-- The supported-source endpoint equation for a quotient-unit-preserving comparison.
This is the source half of the normalized endpoint argument.

Source: coefficient changes (1), supported source endpoint; diagonal limit (3),
normalized source cone.
(blueprint: lem-diagonal-cyclic-quotient-normalized-source-endpoint).

Proof: project the supported source cone equation hs0 to level n. Use the sourceIso
normalization, the finite source comparison and the supported scalar Endpoint's
adjunction equation to identify the full supported quotient generator. The assumed
quotient-unit square he replaces its scalar adjunction unit by M.unit. Apply hsa and
the normalization hs, then cancel the supported finite integral generator between
degree-zero objects, using full faithfulness of the single functor and faithfulness of the
ordinary coefficient forgetful functor. This gives the inverse-source equation.
The empty scheme and n = 0 follow from the same maps and cancellation statements. -/
theorem diagonalCyclicQuotient_normalizedSourceEndpoint
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (source_normalization :
      HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ sourceIso.hom.hom)
        ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
          (eP.underlying.inv.app (SheafOfModules.unit
            (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫
            eP.unitIso.hom.hom)))
 :
  letI : HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.ab (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.abSystems (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.completed (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.completedSystems (ℓ := l) (X := diagonalSurface Y)
  ∀ (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (M : DiagonalCompletedReduction l (diagonalSurface Y))
    (s0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (t0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (hs0 : DiagonalTrace.SupportedSourceConeNormalization l Y D.ordinary s0)
    (ht0 : HEq ((diagonalForget l (diagonalSurface Y)).map t0.hom)
      (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv)
    (n : ℕ) (p : CyclicCartierFrame l Y n)
    (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
          (diagonalImmersion Y)).obj
            (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y))))
    (t : H.obj (op n) ≅ (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
    (hs : DiagonalSourceNormalization l Y D.ordinary n s)
    (ht : DiagonalTrace.FiniteRootNormalization l Y hY H roots n t),
    let F : DerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) ⥤
        DerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y)) :=
      cyclicDiscreteRestriction l (diagonalSurface Y)
    let Rn : DerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) ⥤
        DerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) :=
      cyclicCompletedQuotient l (diagonalSurface Y) M n
    let En : DerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y)) ⥤
        DerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y)) :=
      ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    let K := D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))
    let J := D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)
    ∀ (sa : F.obj (Rn.obj (diagonalCompletedDomain l Y)) ≅ En.obj K)
      (ta : F.obj (Rn.obj (diagonalCompletedCodomain l Y)) ≅ En.obj J),
      F.map ((M.unit n).app (diagonalCompletedDomain l Y)) ≫ sa.hom =
        diagonalSourceLimitMap l Y D a L s0 ≫ (L.projection n).app K →
      F.map ((M.unit n).app (diagonalCompletedCodomain l Y)) ≫ ta.hom =
        diagonalTargetLimitMap l Y D H b L t0 ≫
            (L.projection n).app J →
      ∀ (e : cyclicEvaluationFunctor l Y n eW p ≅ Rn ⋙ F),
        (∀ X : DerivedCategory (DiagonalCompleted l (diagonalSurface Y)),
          (cyclicEvaluationAugmentation l Y n eW p).app X ≫
              (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map (e.hom.app X) =
            (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
              (F.map ((M.unit n).app X))) →
        cyclicEvaluationSource l Y n eW sourceIso p ≫
            e.hom.app (diagonalCompletedDomain l Y) ≫ sa.hom ≫ En.map a.hom ≫
              (((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
                (op n)).mapDerivedCategorySingleFunctor 0).hom.app _ =
          (DerivedCategory.singleFunctor _ 0).map s.inv  := by
  intro D H roots a b L M s0 t0 hs0 ht0 n p s t hs ht
  dsimp only
  intro sa ta hsa hta e he
  let U := diagonalForget l (diagonalSurface Y)
  let Z := diagonalCompletedRestriction l (diagonalSurface Y)
  let V := Mod.forget (D := DiagonalAb (diagonalSurface Y))
    (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) (diagonalSurface Y))
  let R := derivedScalars (cyclicMap l n) (diagonalSurface Y)
  let P := diagonalCompletedSource l Y
  let N := source (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) Y
  let S := DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0
  let q := (eW.F.mapDerivedCategorySingleFunctor 0).app P ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso sourceIso
  let m := p.eW.underlying.inv.app N ≫
    (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)).map
      p.sourceComparison.iso.hom
  let c := (cyclicEvaluationUnderlying l Y n eW p).hom.app
      (diagonalCompletedDomain l Y) ≫
    V.mapDerivedCategory.map (R.map q.hom ≫ p.supported.iso.hom) ≫
    (V.mapDerivedCategorySingleFunctor 0).hom.app N ≫ S.map m
  have hc : IsIso c := by dsimp only [c, m]; infer_instance
  have hsigma := cyclic_source_forward l Y n eW sourceIso p
  change U.mapDerivedCategory.map (cyclicEvaluationSource l Y n eW sourceIso p) ≫ c =
    (U.mapDerivedCategorySingleFunctor 0).hom.app (cyclic_source_object l Y n) at hsigma
  have haug := cyclic_augmentation_forward l Y n eW sourceIso p
  change U.mapDerivedCategory.map ((Z.mapDerivedCategorySingleFunctor 0).inv.app P) ≫
      (cyclicEvaluationAugmentation l Y n eW p).app (diagonalCompletedDomain l Y) ≫ c =
    (U.mapDerivedCategorySingleFunctor 0).hom.app (Z.obj P) ≫
      S.map (eW.underlying.inv.app P ≫ sourceIso.hom.hom ≫
        p.supported.semilinear.hom.hom ≫ m) at haug
  let g : diagonalIntegralSource Y ⟶ U.obj (cyclic_source_object l Y n) :=
    cartierProIntegralGenerator (diagonalResidue.{u} l n) (diagonalImmersion Y)
  have : Epi g := cyclic_generator_epi l Y n
  have : U.Faithful := by unfold U diagonalForget; infer_instance
  dsimp only [cyclicDiscreteRestriction, cyclicCompletedQuotient,
    diagonalCompletedDomain, Functor.comp_obj] at *
  have hγ := generator_augmentation U
    ((Z.mapDerivedCategorySingleFunctor 0).app P)
    (cyclicEvaluationSource l Y n eW sourceIso p)
    ((cyclicEvaluationAugmentation l Y n eW p).app (diagonalCompletedDomain l Y))
    (@asIso _ _ _ _ c hc) (diagonalCompletedGenerator l Y) g
    (eW.underlying.inv.app P ≫ sourceIso.hom.hom ≫ p.supported.semilinear.hom.hom ≫ m)
    hsigma haug
    (source_generator_normalized l Y n eP eW sourceIso source_normalization p)
  have hlimit := single_limit_projection Z L P
    (D.ordinary.E.obj (diagonalIntegralSource Y)) _ s0 a n
  have hproject :
      (cyclicDiscreteRestriction l (diagonalSurface Y)).map
          ((M.unit n).app (diagonalCompletedDomain l Y)) ≫
        sa.hom ≫
        ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
          (op n)).mapDerivedCategory.map a.hom ≫
        (((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
          (op n)).mapDerivedCategorySingleFunctor 0).hom.app _ =
      (Z.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        (DerivedCategory.singleFunctor _ 0).map
          (s0.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) := by
    erw [reassoc_of% hsa]
    unfold diagonalSourceLimitMap
    exact hlimit
  have hs0' := hs0
  unfold DiagonalTrace.SupportedSourceConeNormalization at hs0'
  have hs' := hs
  unfold DiagonalSourceNormalization at hs'
  have hordinary := normalized_inverse U (diagonalCompletedGenerator l Y)
    (s0.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n))
    ((diagonalScalarAdjunction l (diagonalSurface Y)).unit.app (diagonalIntegralSource Y))
    ((D.ordinary.π n).app (diagonalIntegralSource Y)) s g (hs0' n) (eq_of_heq hs')
  exact CyclicAugmentation.endpoint_generator_argument U
    ((Z.mapDerivedCategorySingleFunctor 0).app P)
    (cyclicEvaluationSource l Y n eW sourceIso p) (e.hom.app (diagonalCompletedDomain l Y))
    (sa.hom ≫
      ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
        (op n)).mapDerivedCategory.map a.hom ≫
      (((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
        (op n)).mapDerivedCategorySingleFunctor 0).hom.app _)
    ((cyclicEvaluationAugmentation l Y n eW p).app (diagonalCompletedDomain l Y))
    ((cyclicDiscreteRestriction l (diagonalSurface Y)).map
      ((M.unit n).app (diagonalCompletedDomain l Y)))
    (diagonalCompletedGenerator l Y) g _ s.inv hγ
    (he (diagonalCompletedDomain l Y)) hproject hordinary

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
