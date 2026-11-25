/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Base change of an individual coordinate divisor

The coordinate calculation is independent of coefficients and imposes no flatness
condition on the map of bases.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem coordinate_image {B' B : Scheme.{u}} (g : B' ⟶ B)
    (c : ℕ) (i : Fin c) :
    ((iteratedAffineLineProj B' c ≫ g).toIteratedAffineLine
      (iteratedAffineLine.coord B' c)).appTop '' {iteratedAffineLine.coord B c i} =
      {iteratedAffineLine.coord B' c i} := by
  rw [Set.image_singleton]
  congr 1
  exact Scheme.Hom.toIteratedAffineLine_appTop_coord
    (iteratedAffineLineProj B' c ≫ g) (iteratedAffineLine.coord B' c) i

/-- The map on the closed subschemes cut out by the same coordinate.
Source: the final base-change paragraph of the affine-space zero-section proof
(blueprint: lem-pur-coordinate-divisor-base-change). -/
def coordinateZeroLocusMap {B' B : Scheme.{u}} (g : B' ⟶ B)
    (c : ℕ) (i : Fin c) :
    (iteratedAffineLine B' c).zeroLocusSubscheme {iteratedAffineLine.coord B' c i} ⟶
      (iteratedAffineLine B c).zeroLocusSubscheme {iteratedAffineLine.coord B c i} :=
  ((iteratedAffineLineProj B' c ≫ g).toIteratedAffineLine
    (iteratedAffineLine.coord B' c)).zeroLocusSubschemeMap
    {iteratedAffineLine.coord B c i} {iteratedAffineLine.coord B' c i}
    (by
      rw [Set.image_singleton]
      congr 1
      exact Scheme.Hom.toIteratedAffineLine_appTop_coord
        (iteratedAffineLineProj B' c ≫ g) (iteratedAffineLine.coord B' c) i)

/-- Each coordinate divisor pulls back to the corresponding coordinate divisor.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, final Cartier-map base-change
paragraph (blueprint: lem-pur-coordinate-divisor-base-change).

Proof: the defining map of affine towers pulls back the i-th coordinate to the
same coordinate on the new tower. Hence it maps the singleton set of defining
sections to the primed singleton. The general zero-locus pullback theorem gives
the displayed Cartesian square. This works over arbitrary bases, including the
empty scheme, without flatness. At rank zero there is no index to check. -/
theorem coordinateZeroLocus_isPullback {B' B : Scheme.{u}} (g : B' ⟶ B)
    (c : ℕ) (i : Fin c) :
    IsPullback (coordinateZeroLocusMap g c i)
      ((iteratedAffineLine B' c).zeroLocusSubschemeι {iteratedAffineLine.coord B' c i})
      ((iteratedAffineLine B c).zeroLocusSubschemeι {iteratedAffineLine.coord B c i})
      ((iteratedAffineLineProj B' c ≫ g).toIteratedAffineLine
        (iteratedAffineLine.coord B' c)) := by
  exact Scheme.isPullback_zeroLocusSubschemeι
    ((iteratedAffineLineProj B' c ≫ g).toIteratedAffineLine
      (iteratedAffineLine.coord B' c))
    {iteratedAffineLine.coord B c i} {iteratedAffineLine.coord B' c i}
    (coordinate_image g c i)

end AlgebraicGeometry
