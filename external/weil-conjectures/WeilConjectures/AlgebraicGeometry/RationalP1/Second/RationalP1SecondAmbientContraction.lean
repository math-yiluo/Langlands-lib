/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference

import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondDiagonalInsertionFactor
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondTraceEquation
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondTraceReordering

/-! # Second ambient projective-line contraction
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

-- Keep the fixed geometric coefficient and derived interfaces folded during elaboration.
/-- The second kernel calculation at one object K, for two arrows normalized by
the literal ambient unit and counit formulas.
It concerns the pullback followed by twist and uses no normalized natural transformation.
The completed class need not be a limit class for this calculation. -/
theorem rationalP1_second_ambient_contraction
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
    (family : Family l Y) (_reference : Reference l Y δ family)
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    (_hK : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X Y) K)
    (η : ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ⟶
      (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
            ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)))))
    (ε : (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ⟶ K)
    (_hη : UnitComponentNormalized (coefficient l c).X Y (line l c) (diagram l c Y family)
      (secondLineComparison l c k p hpl Y)
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) η)
    (_hε : CounitComponentNormalized (coefficient l c).X Y (line l c)
      (diagram l c Y family) K ε) :
    η ≫ (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map ε) =
      (ρ_ ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))).inv ≫
        (((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ◁
          ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
            (diagram l c Y family).support₂.hom ≫
            (diagram l c Y family).R₂.R.map (diagram l c Y family).delta ≫
            (diagram l c Y family).trace₂ ≫
            (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫
        (ρ_ ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))).hom := by
  obtain ⟨hb, hp, hη⟩ := _hη
  rw [eq_of_heq hη]
  have hi := second_diagonal_insertion_factor l c k p hpl Y (diagram l c Y family) K
  have ht := second_trace_reordering l c k p hpl Y δ family _reference K _hK ε _hε
  exact assemble_second_unit (coefficient l c).X Y (line l c) (diagram l c Y family)
    (secondLineComparison l c k p hpl Y)
    ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K))
    ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map ε))
    (secondForwardProjection l c k p hpl Y K) hi ht hb hp

end AlgebraicGeometry.ProEtale.RationalP1
