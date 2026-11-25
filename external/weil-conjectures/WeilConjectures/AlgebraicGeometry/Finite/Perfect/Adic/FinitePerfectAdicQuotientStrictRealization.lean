/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientStrictRealizationSquare
import WeilConjectures.CategoryTheory.DerivedCategory.AsFunctorLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryStrictSquare
import WeilConjectures.CategoryTheory.Comma.StructuredArrowUniversalIso
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients

/-! # Strict realization of the quotient coordinates

Source: Stacks Project, Tags 06YY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Inverse image along a weakly etale chart commutes with restriction of fixed scalars; this
is the ordinary comparison localized in `localIsomorphismProEtaleCoefficients`.
Source: Stacks Tag 03DA. -/
def finitePerfectAdicPullbackRestrictIso {Y Z : Scheme.{t}} (g : Z ⟶ Y)
    {R S : Type (t + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    sheafCompose (ProEt.topology Y) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q) ⋙
        ProEtale.upperStar (ModuleCat.{t + 1} R) g ≅
      ProEtale.upperStar (ModuleCat.{t + 1} S) g ⋙
        sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1} q) :=
  letI := ProEt.isContinuous_overPullback g
  normalizationPullbackIso (ProEt.topology Y)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology Z) q

/-- The explicit scalar realizations carry the fixed-scalar coordinates to the strict ordinary
tensor tower restricted to `W`, and the ordinary quotient arrows to its transition maps,
compatibly with the inverse-image comparison and the ordinary scalar compositor.
Source: Stacks Project, Tags 03CY, 03DA and 09C6.

Proof sketch: restriction to `W` of the fixed-scalar coordinates of `N`, followed by
associated module sheafification for the canonical constant scalars, is identified with the
restriction of the ordinary scalar extension of `N` by the counit of associated module
sheafification, since `φ` is the canonical comparison; forgetting along the finite projection
gives `N ⊗ R_n`. On sections both composites of the square send `b ⊗ x` to `q(b) ⊗ x`. -/
theorem finitePerfectAdic_quotient_strict_realization
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (V : X.Etale)
    (δ : ∀ n : ℕ, finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n)
    (hδ : ∀ n : ℕ, FinitePerfectAdicQuotientTransition X d φ V n (δ n))
    (U : V.left.ProEt) (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U) :
    ∃ B : ∀ n : ℕ, finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        ProEtale.upperStar (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
          U.hom ⋙ finitePerfectAdicScalarModules X d V U W f n ≅
        completedAdicOrdinaryTower X d ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (CompletedAdicModules X d)).obj (op n) ⋙
          SheafOfModules.overFunctor (completedAdicRing X d) W,
      ∀ (n : ℕ) (N : CompletedAdicModules X d),
        (finitePerfectAdicScalarModules X d V U W f (n + 1)).map
            ((ProEtale.upperStar
              (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) U.hom).map
                ((δ n).app N) ≫
              (finitePerfectAdicPullbackRestrictIso U.hom (RingHom.ulift.{t + 1, t + 1}
                (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).hom.app
                ((finitePerfectAdicQuotientStrictCoordinates X d φ V n).obj N)) ≫
          (finitePerfectAdicScalarModulesCoherence X d V U W f n).hom.app
            ((ProEtale.upperStar
              (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).obj
                ((finitePerfectAdicQuotientStrictCoordinates X d φ V n).obj N)) ≫
          (B n).hom.app N =
        (B (n + 1)).hom.app N ≫
          (SheafOfModules.overFunctor (completedAdicRing X d) W).map
            (((completedAdicOrdinaryTower X d).obj N).map (homOfLE (Nat.le_succ n)).op) := by
  -- The finite comparisons are determined by their compatibility, so `hφ` is not needed.
  have _ := hφ
  exact ⟨finitePerfectAdicQuotientStrictRealizationIso X d φ hcompat V U W f,
    fun n N ↦ finitePerfectAdicQuotientStrictRealizationIso_square X d φ hcompat V δ hδ U W f n N⟩

end AlgebraicGeometry.Scheme
