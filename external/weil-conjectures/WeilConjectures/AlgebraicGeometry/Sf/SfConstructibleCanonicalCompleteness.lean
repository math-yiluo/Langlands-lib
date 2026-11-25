/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Pbc.PbcIntrinsicTowerComplete
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison

/-! # Presentation witnesses imply canonical actual completeness

The hypothesis is the existential presentation witness. The conclusions
use the actual completed ring, every generating tuple and representative, the
reflector's canonical representative, and the specified strict quotient-tower unit.

## References

* Stacks Tags 0A0E and 099M
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An intrinsic presentation witness makes every actual Koszul unit and the canonical
strict quotient-tower unit invertible. -/
theorem sfConstructibleCanonicalCompleteness
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : PbcCompletedDerived X d) (hM : PbcIsIntrinsicallyComplete X d M) :
    (∀ (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (D : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
      (i : (DerivedCategory.Q.obj D : PbcCompletedDerived X d) ≅ M),
      IsIso (intrinsicCompletionUnit X d r a ha M D i)) ∧
    d.TowerComplete X M := by
  have hTower := pbcIntrinsicComplete_towerComplete d X M hM
  refine ⟨?_, hTower⟩
  intro r a ha D i
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha M D i
  change intrinsicCompletionUnit X d r a ha M D i ≫ c.hom = d.completionUnit X M at hc
  apply (isIso_comp_right_iff _ c.hom).mp
  rw [hc]
  exact hTower

end AlgebraicGeometry.Scheme
