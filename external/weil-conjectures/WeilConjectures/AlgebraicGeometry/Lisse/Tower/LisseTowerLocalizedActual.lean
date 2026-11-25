/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedActualNormalized

/-! # Transport of an actual descended semilinear tower

This is the actual-level part of
localized realization; it has no constant-model comparison or algebraic-arrow assertion.

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03DA
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

/-- The supplied actual comparisons and descent equations transport to one further
pro-étale localization, using the constructed scalar comparison. -/
theorem lisseTower_localized_actual
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom))
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (c : ∀ n : ℕ, LisseTowerScalarSquare (U.hom ≫ g) d n)
    (hc : ∀ n : ℕ, LisseTowerScalarSquareSections (U.hom ≫ g) d n (c n))
    (δ : ∀ n : ℕ, D (n + 1) ⟶
      (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
        (D n))
    (e : ∀ n : ℕ, (lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (hδ : ∀ n : ℕ,
      (lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map (δ n) ≫
          (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n) ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map (e n).hom =
        (e (n + 1)).hom ≫
          adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n)) :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    ∃ actual : ∀ (n : ℕ),
    (L n).obj
      ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n),
    ∀ (n : ℕ),
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual n).hom =
    (H (n + 1)).map (actual (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n := by
  obtain ⟨cmp⟩ := lisseTower_localization_comparisons X Y g d U V W f
  let actual (j : ℕ) := (cmp.level j).app (D j) ≪≫
    (cmp.pull j).mapIso (e j) ≪≫ (cmp.base j).app (M.level j)
  refine ⟨actual, ?_⟩
  intro n
  exact lisseTower_localized_actual_normalized X Y g d M U V W f cmp D c hc δ e hδ n

end AlgebraicGeometry.Scheme
