/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares

/-! # Deriving an ordinary completed coefficient square

Source: coefficient changes, paragraph (1), coefficient/direct-image comparison;
Stacks Tags 05RR and 0941.
(blueprint: lem-diagonal-completed-push-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a v w w'
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- An exact equivalence square has a right-derived comparison fixed by the
full units on complexes, retaining the two independent localization universes.

Source: coefficient changes, paragraph (1); Stacks Tags 05RR and 0941.
(blueprint: lem-diagonal-completed-push-square).

Proof: the two recorded right-derived models have universal cochain units,
hence are left Kan extensions. Precomposition and postcomposition by the two
exact equivalences preserve this universal property. The uniqueness comparison
between the transported universal pairs gives the isomorphism. Its universal
factorization equation is exactly the displayed normalization on each complex. -/
theorem diagonalExactSquare_exists
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w'} C] [HasDerivedCategory.{w'} D]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [U.IsEquivalence] [V.IsEquivalence]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G) :
    Nonempty (DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary) := by
  let := RF.universal
  let := RG.universal
  let := Functor.IsRightDerivedFunctor.isLeftKanExtension RF.R RF.η
    (HomologicalComplex.quasiIso A (.up ℤ))
  let := Functor.IsRightDerivedFunctor.isLeftKanExtension RG.R RG.η
    (HomologicalComplex.quasiIso C (.up ℤ))
  have : U.asEquivalence.functor.Additive := by
    change U.Additive
    infer_instance
  have : V.asEquivalence.functor.Additive := by
    change V.Additive
    infer_instance
  obtain ⟨e, he⟩ := CategoryTheory.rightDerivedSquare U.asEquivalence V.asEquivalence
    F G RF.R RG.R RF.η RG.η ordinary
  exact ⟨⟨e, he⟩⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
universe u

/-- The ordinary coefficient square, before applying right derivation.
Source: coefficient changes, initial coefficient identification.
(blueprint: lem-diagonal-completed-push-square). -/
structure CompletedOrdinarySquare (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S) where
  ordinary : diagonalTracePush l f ⋙ eS.F ≅
    eX.F ⋙ CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  normalization : ∀ M : DiagonalCompleted l X,
    HEq ((ordinary.hom.app M).hom ≫
        (lowerStar Ab.{u + 1} f).map (eX.underlying.hom.app M))
      (eS.underlying.hom.app ((diagonalTracePush l f).obj M))

/-- Derive an ordinary square by its universal-unit-normalized comparison.
The normalization uniquely fixes the derived isomorphism by the two universal
right-derived units. Source: coefficient changes, paragraph (1).
(blueprint: lem-diagonal-completed-push-square). -/
def CompletedOrdinarySquare.derive
    {l : ℕ} [Fact l.Prime] {X S : Scheme.{u}} {f : X ⟶ S}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {eX : CompletedRealization l X} {eS : CompletedRealization l S}
    (s : CompletedOrdinarySquare l f eX eS)
    {R : DiagonalRightDerived (diagonalTracePush l f)}
    {R' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)} :
    CompletedPushSquare l f eX eS R R' where
  ordinary := s.ordinary
  ordinary_normalization := s.normalization
  derived := (diagonalExactSquare_exists _ _ _ _ R R' s.ordinary).some

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
