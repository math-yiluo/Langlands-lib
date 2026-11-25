/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1SectionEvaluation
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
public import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceData
import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTracePretrace
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ProjectionScalarEvaluation

/-! # Expanded counit equality for the terminal first projective-line trace
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison
attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] twist projectionMap singleUnitIso
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientExchange
attribute [local irreducible] internalMonoidal
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

-- STATEMENT-DISPUTED (old version): Diagram leaves traceq unrelated to trace₁.
/-- Expanded counit transport for a diagram satisfying scalar trace base change.

The scalar trace square is necessary: Diagram does not relate its q trace to its
first-projection trace. The trace-free Kunneth comparison first transports the
projection part. Tensoring the scalar square and applying projection unitality
then gives the asserted terminal trace equation. -/
theorem rationalP1_first_trace_transport_counit_expanded_for_diagram
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (d : Diagram (coefficient l c).X Y (line l c))
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (hq : IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y)
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)))
    (h₁ : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
    (ht : firstTraceExchange (coefficient l c).X Y
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
        (secondLineComparison l c k p hpl Y) ≫
      firstNativeFunctional (coefficient l c).X Y (line l c) d
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) d.trace₁ ≫
      (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (trace (coefficient l c).X Y (line l c) d ≫
          (singleUnitIso (coefficient l c).X Y).hom) ≫
        (secondTraceUnitIso (coefficient l c).X Y).hom) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (X := (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
            (line l c (diagonalSurface Y))
            ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)) hp ≫
        (twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)) ≫
      counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y))
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) hq ≫
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ◁
        (trace (coefficient l c).X Y (line l c) d ≫
          (singleUnitIso (coefficient l c).X Y).hom)) ≫
      (ρ_ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)).hom =
    firstTerminalFunctional (coefficient l c).X Y (line l c) d M
      (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      d.trace₁ h₁ := by
  have hf := first_trace_pretrace l c k p hpl Y d M hq hb hp h₁ d.trace₁
  have hs := projectionMate_scalar_evaluation l c Y M
    ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
      (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))
    _ _
    ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (X := (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
            (line l c (diagonalSurface Y))
            ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)) hp ≫
        (twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)))
    (counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y))
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) hq)
    ((moduleObjectDerivedPushforward (coefficient l c).X (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))
    (unit (coefficient l c).X (ProjectiveLine Y))
    (firstTraceExchange (coefficient l c).X Y
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      (secondLineComparison l c k p hpl Y))
    (firstNativeFunctional (coefficient l c).X Y (line l c) d
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) d.trace₁)
    (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom
    (trace (coefficient l c).X Y (line l c) d ≫ (singleUnitIso (coefficient l c).X Y).hom) ht
  exact hs.symm.trans hf

end AlgebraicGeometry.ProEtale.RationalP1
