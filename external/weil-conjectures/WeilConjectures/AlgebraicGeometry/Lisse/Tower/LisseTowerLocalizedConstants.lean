/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexComparisons

/-! # Constant complexes in the localized fixed realization

This is the constant-complex
part of localized realization, independent of any descended or normalized tower.
The three scheme morphisms need no relation to one another.

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03DA
* Sites, Tag 0H7J
* Cohomology on Sites, Tag 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/-- Constant models and their semilinear normalization square exist for the specified scalar
comparison. -/
theorem lisseTower_localized_constants
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d j
    ∃ model : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (L n).obj ((localProEtaleComparison a
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant S.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization g d n).obj E,
    ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection g d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model j N) ≪≫
        ((constantAdicQuotientRightIso g d j).app N).symm
    (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization a (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow S.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (lisseTowerPulledScalarIso g b d n).hom.app
      ((localProEtaleComparison a
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization g d).map (lisseTowerAlgebraArrow d n k) := by
  dsimp
  obtain ⟨model, hmodel⟩ := lisseTower_constant_complex_comparisons g a b d
  refine ⟨fun n E ↦ (model n).app E, ?_⟩
  exact lisseTower_localized_constants_normalization g a b d model hmodel

end AlgebraicGeometry.Scheme
