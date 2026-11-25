/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1SectionEvaluation
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingProjection
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingPreservation
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LineFromPreservation
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference

import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceTransportCore

/-! # Transporting the terminal first projective-line trace
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
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

-- Keep the fixed geometric coefficient and derived interfaces folded during elaboration.
/-- Transport the terminal trace functional before any diagonal class is inserted.
This equation has source Rq_*Rp₂*(p₁*M tensor T_W), rather than Rq_*M, and contains
neither a diagonal class insertion nor a unit component. -/
theorem rationalP1_first_trace_transport
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (hM : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y)) M)
    (ε : (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward (coefficient l c).X
            (ProjectiveLine Y ↘ Y)).obj M))) ⟶
        (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)
    (hε : CounitComponentNormalized (coefficient l c).X Y (line l c)
      (diagram l c Y family)
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) ε)
    (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M))) :
    ∃ h₁ : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)),
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
      ε =
    firstTerminalFunctional (coefficient l c).X Y (line l c) (diagram l c Y family) M
      (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      (diagram l c Y family).trace₁ h₁ := by
  have hc := localizingPreservationChecks l c k p hpl Y
  let hP : (ProjectiveLine Y).Over (Spec (.of k)) :=
    ⟨(ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  let hW : (diagonalSurface Y).Over (Spec (.of k)) :=
    ⟨firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))⟩
  letI : (ProjectiveLine Y).Over (Spec (.of k)) := hP
  letI : (diagonalSurface Y).Over (Spec (.of k)) := hW
  letI : LocallyOfFiniteType (ProjectiveLine Y ↘ Spec (.of k)) :=
    hc.geometry.standingP.2.1
  letI : QuasiCompact (ProjectiveLine Y ↘ Spec (.of k)) :=
    hc.geometry.standingP.2.2
  letI : IsSeparated (ProjectiveLine Y ↘ Spec (.of k)) := hc.geometry.standingP.1
  letI : LocallyOfFiniteType (diagonalSurface Y ↘ Spec (.of k)) :=
    hc.geometry.standingW.2.1
  letI : QuasiCompact (diagonalSurface Y ↘ Spec (.of k)) :=
    hc.geometry.standingW.2.2
  letI : IsSeparated (diagonalSurface Y ↘ Spec (.of k)) := hc.geometry.standingW.1
  letI : (firstProjection Y).IsOver (Spec (.of k)) := ⟨rfl⟩
  letI : IsProper (firstProjection Y) := hc.geometry.properFirst
  have hline : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X (diagonalSurface Y))
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) := by
    apply line_localizing_of_preservation (coefficient l c).X
      (f := firstProjection Y) (L := line l c (diagonalSurface Y))
    intro K hK
    exact hc.objectsW.twist.preserves _ (hc.pullFirst.preserves K hK)
  have h₁ : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)) :=
    projectionMap_isIso_localizing l c k p hpl (firstProjection Y) M _ hM hline
  exact ⟨h₁, rationalP1_first_trace_transport_core l c k p hpl Y δ family reference M hM ε
    hε hb hp h₁⟩

end AlgebraicGeometry.ProEtale.RationalP1
