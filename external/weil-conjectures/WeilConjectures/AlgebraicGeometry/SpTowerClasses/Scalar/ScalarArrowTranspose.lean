/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarChernArrow
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.ScalarRootTranspose
import WeilConjectures.AlgebraicGeometry.ScalarData.ScalarModelUnit
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedScalarArrow
/-! # Scalar extension transposes to the ordinary root unit -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings

/-- Scalar extension followed by restriction is the integral arrow followed by
its ordinary scalar unit, with the prescribed normalized source.
Source: classes proof (2), Stacks 06YY and 07A6.
(blueprint: lem-sfb-scalar-arrow-transpose).
Proof: the section and representative equations fix the scalar adjunction, so
its unit commutes with the specified canonical scalar shift. The source equation
is unitNormalization and the target equation is scalarRootTranspose. Naturality
of the unit applied to f combines these two equations. -/
theorem scalarArrowTranspose (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hc : unitNormalization c.scalar.T
      (SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T))
      c.scalar.adjunction c.scalarUnit (scalarGenerator l E T))
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
        (scalarGenerator l E T) ≫
      mapSingleArrow (SemilinearSections.res (coefficientSystemMap l E T)) (2 : ℤ)
        (scalarChernArrow l E c f) =
      f ≫ ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
        (c.scalar.ordinaryAdjunction.unit.app c.rootModule))⟦(2 : ℤ)⟧' := by
  let G := SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T)
  have had : c.scalar.adjunction.CommShift ℤ := by
    rw [c.scalar.adjunction_eq]
    exact Adjunction.commShift_of_rightAdjoint
      (C := DerivedCategory (Systems T (Rrings l T)))
      (D := DerivedCategory (Systems T (Arings l E T)))
      (F := c.scalar.T) (G := G.mapDerivedCategory)
      (SheafOfModules.sheafScalarDerivedAdjunction
        (coefficientSystemMap l E T) c.scalar.model) ℤ
  let := had
  have hx := hc
  dsimp only [unitNormalization] at hx
  simp only [Adjunction.homEquiv_unit, Category.assoc] at hx
  have hy := scalarRootTranspose l E c
  simp only [Adjunction.homEquiv_unit, Category.assoc] at hy
  exact normalizedScalarArrow_transpose c.scalar.T G.mapDerivedCategory c.scalar.adjunction
    c.scalarUnit (lineComparison l E c)
    ((G.mapDerivedCategorySingleFunctor 0).app (coefficient T (Arings l E T)))
    ((G.mapDerivedCategorySingleFunctor 0).app (lineModule l E c))
    _ _ hx hy (2 : ℤ) f
end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
