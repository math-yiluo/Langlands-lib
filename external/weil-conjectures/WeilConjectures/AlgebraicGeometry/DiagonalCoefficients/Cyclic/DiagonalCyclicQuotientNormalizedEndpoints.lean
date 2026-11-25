/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientNormalizedSourceEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientNormalizedTargetEndpoint

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

set_option linter.unusedVariables false in
/-- A quotient-unit-preserving comparison has the supported-source and root squares.
This assertion assumes the comparison, and constructs no quotient functor comparison.

Source: coefficient changes (1), supported and root endpoints; diagonal limit (3),
normalized source and root cones
(blueprint: lem-diagonal-cyclic-quotient-normalized-endpoints).

Proof: project the supported source cone equation hs0 to n. Use the sourceIso
normalization, the finite source comparison and the supported scalar Endpoint's
adjunction equation to identify the full supported quotient generator. The assumed
quotient-unit square replaces its scalar adjunction unit by M.unit. Apply hsa and
the normalization hs, then cancel the quotient projection (which is epic on this
flat degree-zero supported coefficient). This gives the inverse-source equation.
For the root endpoint, ht0 identifies each limit projection with the actual root
projection. IntegralRoots uniqueness identifies the two integral-root maps.
The finite root maps coincide because their inclusions into the units sheaf agree
and that inclusion is monic. Use p.lineEndpoint.normalization and ht, transpose
p.line.iso by scalar adjunction, and apply the assumed quotient-unit square and hta.
The root quotient is a flat rank-one finite line, so its normalized unit detects
the remaining degree-zero map. Exact-single and shift naturality give the displayed
shifted equation. No derived arrow is inferred merely from its finite evaluations;
the cancellation is only at these prescribed flat coefficient endpoints. The empty
scheme and n=0 follow from the same maps and cancellation statements. -/
theorem diagonalCyclicQuotient_normalizedEndpoints
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
          (DerivedCategory.singleFunctor _ 0).map s.inv ∧
        En.map b.inv ≫ ta.inv ≫ e.inv.app (diagonalCompletedCodomain l Y) ≫
            cyclicEvaluationTarget l Y n eW p =
          (En.commShiftIso (2 : ℤ)).hom.app _ ≫
            ((((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
              (op n)).mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧' ≫
            ((DerivedCategory.singleFunctor _ 0).map t.hom)⟦(2 : ℤ)⟧' := by
  intro D H roots a b L M s0 t0 hs0 ht0 n p s t hs ht
  dsimp only
  intro sa ta hsa hta e he
  constructor
  · exact diagonalCyclicQuotient_normalizedSourceEndpoint l Y hY eP eW sourceIso
      source_normalization D H roots a b L M s0 t0 hs0 ht0 n p s t hs ht sa ta hsa hta e he
  · exact diagonalCyclicQuotient_normalizedTargetEndpoint l Y hY eP eW sourceIso
      source_normalization D H roots a b L M s0 t0 hs0 ht0 n p s t hs ht sa ta hsa hta e he

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
