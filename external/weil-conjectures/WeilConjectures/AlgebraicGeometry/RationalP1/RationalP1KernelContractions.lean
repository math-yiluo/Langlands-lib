/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference

import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstAmbientContraction
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondAmbientContraction

/-! # Ambient rational projective-line kernel contractions

This is the geometric calculation preceding integration in the rational
projective-line triangle argument. It uses normalization by the explicit
diagonal-class and trace pastes, and asserts the kernel formulas before integration.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison

-- The canonical ambient pastes use the existing unit/counit elaboration allowance.
/-- The ambient diagonal-class insertion and trace contraction give the two kernel
integrals. This statement concerns the ambient pastes for any pair of natural transformations
whose components have the specified canonical normalization. No adjunction is assumed. -/
theorem rationalP1_kernel_contractions
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (family : Family l Y) (_reference : Reference l Y δ family)
    (a : UnitCounitType l c k p hpl Y)
    (_hnorm : UnitCounitNormalized l c k p hpl Y family a) :
    (∀ M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y),
      ((push l c k p hpl Y).map (a.1.app M) ≫
        a.2.app ((push l c k p hpl Y).obj M)).hom =
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (((ρ_ (M.obj)).inv ≫ ((M.obj) ◁
          ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
            (diagram l c Y family).support₁.hom ≫
            (diagram l c Y family).R₁.R.map (diagram l c Y family).delta ≫
            (diagram l c Y family).trace₁ ≫
            (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫ (ρ_ (M.obj)).hom))) ∧
    (∀ K : rationalLocalizingCategory (coefficient l c).X Y,
      (a.1.app ((exceptional l c k p hpl Y).obj K) ≫
        (exceptional l c k p hpl Y).map (a.2.app K)).hom =
      (ρ_ (((exceptional l c k p hpl Y).obj K).obj)).inv ≫
        ((((exceptional l c k p hpl Y).obj K).obj) ◁
          ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
            (diagram l c Y family).support₂.hom ≫
            (diagram l c Y family).R₂.R.map (diagram l c Y family).delta ≫
            (diagram l c Y family).trace₂ ≫
            (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫
        (ρ_ (((exceptional l c k p hpl Y).obj K).obj)).hom) := by
  constructor
  · intro M
    change ((moduleObjectDerivedPushforward (coefficient l c).X
      (ProjectiveLine Y ↘ Y)).map (a.1.app M).hom ≫
        (a.2.app ((push l c k p hpl Y).obj M)).hom :
        (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M.obj ⟶
          (moduleObjectDerivedPushforward (coefficient l c).X
            (ProjectiveLine Y ↘ Y)).obj M.obj) = _
    exact rationalP1_first_ambient_contraction l c k p hpl Y δ family _reference
        M.obj M.property (a.1.app M).hom
        (a.2.app ((push l c k p hpl Y).obj M)).hom
        (_hnorm.1 M) (_hnorm.2 ((push l c k p hpl Y).obj M))
  · intro K
    change ((a.1.app ((exceptional l c k p hpl Y).obj K)).hom ≫
      (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
          (a.2.app K).hom) :
        ((exceptional l c k p hpl Y).obj K).obj ⟶
          ((exceptional l c k p hpl Y).obj K).obj) = _
    exact rationalP1_second_ambient_contraction l c k p hpl Y δ family _reference
      K.obj K.property (a.1.app ((exceptional l c k p hpl Y).obj K)).hom
      (a.2.app K).hom (_hnorm.1 ((exceptional l c k p hpl Y).obj K)) (_hnorm.2 K)

end AlgebraicGeometry.ProEtale.RationalP1
