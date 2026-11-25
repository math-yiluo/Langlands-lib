/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison

/-!
# Inverse image of the consecutive-quotient Tor sheaf

The consecutive-quotient Tor sheaf of the degree-`q` cohomology of a reduction commutes
with inverse image: its inverse image only depends on the inverse image of the complex.

## References

* Stacks Tags 0D6D and 06YY
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {T S : Scheme.{u}} (g : S ⟶ T) (q : ℤ) (n : ℕ)

/-- The inverse image of the consecutive-quotient Tor sheaf of the degree-`q` cohomology of
the `n+1`-st reduction is computed from the inverse image of the complex. -/
private def torPullIso (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :
    (proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
        ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n))) (Iso.refl _)).obj
      ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((pbcCompletedReduction T d (n + 1)).obj K))))) ≅
      (DerivedCategory.homologyFunctor _ (-1)).obj
        ((pbcDerivedExtend ((adicTowerInverseImage g).map
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((pbcDerivedExtend ((adicTowerInverseImage g).map
                  (pbcAdicProjection T d (n + 1)))).obj
                ((adicTowerPullback g (pbcAdicCompletion T d)).obj K))))) :=
  let Pn := proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
    ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n))) (Iso.refl _)
  let Pn₁ := proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op (n + 1)))
    ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op (n + 1)))) (Iso.refl _)
  (Pn.mapDerivedCategoryHomologyFunctorIso (-1)).app _ ≪≫
    (DerivedCategory.homologyFunctor _ (-1)).mapIso
      ((scalarPullIso g (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).app _ ≪≫
        (pbcDerivedExtend _).mapIso ((Pn₁.mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            ((Pn₁.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
              (DerivedCategory.homologyFunctor _ q).mapIso
                ((scalarPullIso g (pbcAdicProjection T d (n + 1))).app K))))

/-- Complexes with isomorphic inverse images have isomorphic inverse images of their
consecutive-quotient Tor sheaves. -/
theorem nonempty_pullback_tor_iso {K L : DerivedCategory (pbcModules T (pbcAdicCompletion T d))}
    (e : (adicTowerPullback g (pbcAdicCompletion T d)).obj K ≅
      (adicTowerPullback g (pbcAdicCompletion T d)).obj L) :
    let tor (M : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) :=
      (DerivedCategory.homologyFunctor _ (-1)).obj
        ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((pbcCompletedReduction T d (n + 1)).obj M))))
    let Pn := proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
      ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n))) (Iso.refl _)
    Nonempty (Pn.obj (tor K) ≅ Pn.obj (tor L)) :=
  ⟨torPullIso d g q n K ≪≫
    (DerivedCategory.homologyFunctor _ (-1)).mapIso ((pbcDerivedExtend _).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso ((DerivedCategory.homologyFunctor _ q).mapIso
        ((pbcDerivedExtend _).mapIso e)))) ≪≫ (torPullIso d g q n L).symm⟩

end AlgebraicGeometry.Scheme
