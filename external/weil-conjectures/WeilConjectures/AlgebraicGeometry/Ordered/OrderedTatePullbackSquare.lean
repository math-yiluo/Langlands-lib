/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition

/-! # The ordered Tate comparison around a commutative square

## References

* Tate pullback and transposition paragraph
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The ordered finite Tate comparisons commute around any square of scheme maps. -/
theorem orderedTatePullbackSquare (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y X' Y' : Scheme.{u}} (s : Y ⟶ X) (s' : Y' ⟶ X')
    (b : Y' ⟶ Y) (v : X' ⟶ X) (hs : s' ≫ v = b ≫ s)
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (hX' : IsUnit (N : Γ(X', ⊤))) (d : ℕ) :
    (ordinaryFinitePullback A b).map
        (vectorIntegrationBaseCoefficientPullback A N hA t s hX d).inv ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b s).inv.app
        (affineLinearBaseCoefficient A N hA X d) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' v (b ≫ s) hs.symm).hom.app
        (affineLinearBaseCoefficient A N hA X d) ≫
      (ordinaryFinitePullback A s').map
        (vectorIntegrationBaseCoefficientPullback A N hA t v hX d).hom =
    (vectorIntegrationBaseCoefficientPullback A N hA t b hY d).hom ≫
      (vectorIntegrationBaseCoefficientPullback A N hA t s' hX' d).inv := by
  apply (cancel_mono
    (vectorIntegrationBaseCoefficientPullback A N hA t s' hX' d).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id]
  have hb := orderedTateCoefficientComposition A N hA t b s (b ≫ s) rfl hX hY d
  have hs' := orderedTateCoefficientComposition A N hA t s' v (b ≫ s)
    hs.symm hX hX' d
  rw [hs']
  rw [← hb]
  simp only [Iso.inv_hom_id_app_assoc]
  have hmap := (ordinaryFinitePullback A b).map_comp
    (vectorIntegrationBaseCoefficientPullback A N hA t s hX d).inv
    (vectorIntegrationBaseCoefficientPullback A N hA t s hX d).hom
  rw [← Category.assoc, ← hmap]
  simp

end AlgebraicGeometry.Etale
