/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerScalarRestriction

/-! # The coefficient square after a further fixed-coefficient inverse image

The square is built from the
section-normalized ordinary coefficient square, the exact inverse-image coefficient
mate, and the specified restriction-of-scalars compositor.

## References

* Stacks Tags 03CY and 03DA
* Stacks Tags 03DA and 05RU
* Stacks Tags 03DA and 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicFiniteProjection

/-- The uniquely specified ordinary coefficient square at the final scheme.
Its defining property determines the square on all underlying abelian sections. -/
def lisseTowerNormalizedScalarSquare {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    LisseTowerScalarSquare g d n :=
  (lisseTower_scalar_restriction g d n).exists.choose

/-- The chosen square has the section normalization, independent of any tower. -/
theorem lisseTowerNormalizedScalarSquare_sections {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    LisseTowerScalarSquareSections g d n (lisseTowerNormalizedScalarSquare g d n) :=
  (lisseTower_scalar_restriction g d n).exists.choose_spec.1

/-- Localize the fixed-realization square without an etale comparison functor. -/
def lisseTowerFixedScalarIso {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare g d n) :
    normalizationRestrict (ProEt.topology Z) (lisseTowerEtaleQuotient d n) ⋙
        lisseTowerFixedRealization g d (n + 1) ≅
      lisseTowerFixedRealization g d n ⋙
        pbcDerivedRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) := by
  unfold pbcDerivedRestrict
  exact Functor.isoWhiskerLeft
      (normalizationRestrict (ProEt.topology Z) (lisseTowerEtaleQuotient d n))
      (lisseTowerFixedRealizationIso g d (n + 1)).symm ≪≫
    Functor.mapDerivedCategorySquareIso c ≪≫
    Functor.isoWhiskerRight (lisseTowerFixedRealizationIso g d n)
      (pbcRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).mapDerivedCategory

/-- The scalar comparison for inverse image followed by fixed realization, after
restriction to the actual inverse image of the constant completion ring.
This is a paste of specified comparisons, with no choice of a local tower or arrow. -/
def lisseTowerPulledScalarIso {X Z T : Scheme.{u}} (g : Z ⟶ X) (h : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    normalizationRestrict (ProEt.topology T) (lisseTowerEtaleQuotient d n) ⋙
        ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))
          h).mapDerivedCategory ⋙ lisseTowerFixedRealization g d (n + 1)) ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection g d (n + 1)) ≅
      ((ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
          h).mapDerivedCategory ⋙ lisseTowerFixedRealization g d n) ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection g d n) := by
  let P (j : ℕ) := (ProEtale.upperStar
    (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) h).mapDerivedCategory
  let F (j : ℕ) := lisseTowerFixedRealization g d j
  let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection g d j)
  let R := pbcDerivedRestrict ((adicTowerInverseImage g).map
    (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
  let a := localIsomorphismProEtaleCoefficients h (lisseTowerEtaleQuotient d n)
  let b := lisseTowerFixedScalarIso g d n (lisseTowerNormalizedScalarSquare g d n)
  let k := pbcDerivedRestrictComp (constantAdicFiniteProjection g d (n + 1))
    ((adicTowerInverseImage g).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    (constantAdicFiniteProjection g d n)
    (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))
  exact Functor.isoWhiskerRight
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight a (F (n + 1)) ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (P n) b ≪≫
        (Functor.associator _ _ _).symm) (H (n + 1)) ≪≫
    Functor.associator (P n ⋙ F n) R (H (n + 1)) ≪≫
    Functor.isoWhiskerLeft (P n ⋙ F n) k ≪≫
    (Functor.associator (P n) (F n) (H n)).symm

end AlgebraicGeometry.Scheme
