/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateDerivedComparison

/-! # The two-label affine comparison family
Source: Stacks Project, Tags 08DW and 06Y1.
(blueprint: lem-pc-affine-coordinate-comparison-family-base). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The chart object comparisons assemble to a natural comparison on the induced
category of the two labelled models. Naturality is the preceding chart naturality
lemma, applied to all four possible labels and all cross-label morphisms.
Source: Stacks Project, Tag 08DW(2).
(blueprint: lem-pc-affine-coordinate-comparison-family-base). -/
theorem exists_affineCoordinateComparisonFamilyBase :
    ∃ δ : AffineCoordinateComparisonFamily.{u, w},
      ∀ (a b : AffineComparisonCoordinate.{u, w})
        (φ : a.A →+* b.A) (p : b.X ⟶ a.X)
        (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
        (M N : CochainComplex (ModuleCat.{u} a.A) ℤ)
        (hM : AffineComparisonKFlat a.A M) (hN : AffineComparisonKFlat a.A N)
        (j : Bool),
        (δ a b φ p hp M N hM hN).app j =
          affineCoordinateChartObjectComparison a b φ p hp
            (cond j M N) (by cases j <;> assumption) := by
  refine ⟨affineCoordinateDerivedComparison, ?_⟩
  intro a b φ p hp M N hM hN j
  rfl

end AlgebraicGeometry
