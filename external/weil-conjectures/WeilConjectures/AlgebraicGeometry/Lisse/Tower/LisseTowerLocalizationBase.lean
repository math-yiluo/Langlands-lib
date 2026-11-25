/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationTransport
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationCoherence

/-! # The coefficient component of the finite inverse-image composition comparison

## References

* Stacks Project, Modules on Sites, Tags 03CY, 03D2, 03D3
* Cohomology on Sites, Tag 0D6D
* Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03D3
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicFiniteProjection lisseTowerLocalizationPull
  lisseTowerLocalizationScalar lisseTowerInverseImageScalar

/-- Composition for the actual finite-ring inverse image, expressed through the fixed
realization equivalence, with compatibility at the coefficient mate component alone.
This involves no etale comparison functor, etale arrow, tower or level marking.
-/
theorem lisseTower_localization_base {X Z S T : Scheme.{u}}
    (t : Z ⟶ X) (s : T ⟶ X) (a : T ⟶ S) (b : S ⟶ Z)
    (h : a ≫ b ≫ t = s) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃ e : ∀ n : ℕ,
      adicTowerPullback t ((pbcAdicRings X d).obj (op n)) ⋙
          lisseTowerLocalizationPull t s a b d n ≅
        adicTowerPullback s ((pbcAdicRings X d).obj (op n)),
    ∀ (n : ℕ) (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))),
      let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection s d j)
      (lisseTowerLocalizationPull t s a b d (n + 1) ⋙ H (n + 1)).map
          ((lisseTowerInverseImageScalar t d n).hom.app N) ≫
          (lisseTowerLocalizationScalar t s a b d n).hom.app
            ((adicTowerPullback t ((pbcAdicRings X d).obj (op n))).obj N) ≫
          (H n).map ((e n).hom.app N) =
        (H (n + 1)).map ((e (n + 1)).hom.app
          ((pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj N)) ≫
          (H (n + 1)).map ((lisseTowerInverseImageScalar s d n).hom.app N) ≫
          (pbcDerivedRestrictComp (constantAdicFiniteProjection s d (n + 1))
            ((adicTowerInverseImage s).map
              (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
            (constantAdicFiniteProjection s d n)
            (constantAdicFiniteProjection_comp s d (n + 1) n (Nat.le_succ n))).hom.app
              ((adicTowerPullback s ((pbcAdicRings X d).obj (op n))).obj N) := by
  subst h
  exact ⟨lisseTowerChainLevel t b a d, fun n N ↦ lisseTowerChainLevel_scalar t b a d n N⟩

end AlgebraicGeometry.Scheme
