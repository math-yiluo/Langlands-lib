/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantResidueComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedLocalPerfectCriterion

/-!
# Completed realization of a module over a finite quotient

For a module `N` over `A/I^{n+1}`, the completed realization of `N` (viewed as an
`A`-module) is the constant sheaf of `N`, with the completed ring acting through the
projection to the `n`-th quotient ring.

## References

* Bhatt--Scholze, Proposition 6.6.11
* Stacks Tags 093J and 093M
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The completed realization of a module over `A/I^{n+1}` is its constant sheaf, restricted
to the completed coefficients through the `n`-th projection. -/
theorem nonempty_integralConstantModule_restrictScalars_iso (n : ℕ)
    (N : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) :
    Nonempty ((integralConstantModule T d).obj
        ((ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj N) ≅
      (pbcRestrict (pbcAdicProjection T d n)).obj
        ((pbcRestrict (pbcLevelConstantComparison T d n).inv).obj
          ((adicLisseConstantModules T (A ⧸ d.ideal ^ (n + 1))).obj N))) := by
  have := d.noetherian
  let e := pbcCompletedComparison T d
  let π := limit.π (adicLisseRingSystem T d.ideal) (op n)
  let c := CompletedConstantReduction.base T d.ideal ≫ e.hom
  have hc (m : ℕ) : c ≫ e.inv ≫ limit.π (adicLisseRingSystem T d.ideal) (op m) =
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (m + 1)))) := by
    simp only [c, Category.assoc, Iso.hom_inv_id_assoc]
    exact (CompletedConstantReduction.base_exists T d.ideal).choose_spec.1 m
  have hp : pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv = e.inv ≫ π := by
    dsimp only [e, π, pbcAdicProjection, pbcCompletedComparison]
    rw [HasLimit.isoOfNatIso_inv_π]
    rfl
  have := scalarResidueMap_isIso T d.ideal e c hc n N
  exact ⟨(ordinaryConstantModel T d).app _ ≪≫
    asIso ((scalarResidueMap T (Ideal.Quotient.mk (d.ideal ^ (n + 1))) c (e.inv ≫ π)
      (hc n)).app N) ≪≫
    ((pbcRestrictComp (pbcAdicProjection T d n) (pbcLevelConstantComparison T d n).inv
      (e.inv ≫ π) hp).app _).symm⟩

end AlgebraicGeometry.Scheme
