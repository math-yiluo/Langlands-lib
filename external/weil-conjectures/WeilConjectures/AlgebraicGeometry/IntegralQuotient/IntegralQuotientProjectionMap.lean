/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap

/-! # Integral quotient comparison for unbounded direct image

The mate is formed with the actual derived adjunctions. Quotient levels are indexed by
n + 1 and every tensor product is the ordinary, uncompleted derived tensor product.

## References

* Stacks 0D6D, cartesian coefficients
* Stacks 0G7E
* Stacks 0944, 0B56
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual ordinary cartesian identification of the restricted quotient coefficient. -/
def coefficientPull₀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (CondensedRing.upperStar (integral l E) f).obj (B₀ (reduction l E n) Y) ≅
      B₀ (reduction l E n) X :=
  (CondensedRing.comapUpperStarIso (reduction l E n) f).symm.app _ ≪≫
    (V₀ (reduction l E n) X).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar (finite l E n) f)).symm

/-- The canonical inverse-image computation at a cochain representative. -/
def computePull {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules Λ Y) ℤ) :
    (L Λ f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P) :=
  (L Λ f).map ((DerivedCategory.quotientCompQhIso (Modules Λ Y)).inv.app P) ≫
    (pullCounit f).app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((CondensedRing.upperStar Λ f).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (Modules Λ X)).hom.app
      (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)

/-- The specified coefficient pullback arrow in the derived category. -/
def coefficientPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (L (integral l E) f).obj (B (reduction l E n) Y) ⟶ B (reduction l E n) X :=
  computePull f ((CochainComplex.singleFunctor _ 0).obj (B₀ (reduction l E n) Y)) ≫
    DerivedCategory.Q.map
      (((CondensedRing.upperStar (integral l E) f).mapCochainComplexSingleFunctor 0).hom.app
          (B₀ (reduction l E n) Y) ≫
        (CochainComplex.singleFunctor _ 0).map (coefficientPull₀ l E f n).hom)

/-- The perfect-coefficient projection arrow: the recorded module-object projection map
(the counit transpose of the specified derived tensor-pullback comparison followed by the
integral counit), followed by the direct image of the actual cartesian pullback of the
quotient coefficient. -/
@[irreducible] def projectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : DerivedCategory (Modules (integral l E) X)) :
    (F (integral l E) f).obj K ⊗ B (reduction l E n) Y ⟶
      (F (integral l E) f).obj (K ⊗ B (reduction l E n) X) := by
  have c := coefficientPull l E f n
  unfold L CondensedRing.moduleObjectDerivedPullback at c
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact CondensedRing.moduleObjectProjectionMap (integral l E) f K
      (B (reduction l E n) Y) ≫
    (CondensedRing.lowerStar (integral l E) f).rightDerivedFunctor.map (K ◁ c)

end AlgebraicGeometry.ProEtale.IntegralQuotient
