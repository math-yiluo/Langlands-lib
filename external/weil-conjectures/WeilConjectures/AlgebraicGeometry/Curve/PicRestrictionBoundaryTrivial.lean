/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard

/-!
# Boundary-point classes restrict to the identity

Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine,
first paragraph, restriction and boundary divisors
(blueprint: lem-sc-pic-restriction-boundary-trivial).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The point-ideal class of a point outside the open curve restricts to the identity.
Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine, first paragraph;
restriction and boundary divisors, steps 3 and 4 of lem-sc-pic-restriction-exact
(blueprint: lem-sc-pic-restriction-boundary-trivial).

Proof: The inverse image of the closed point P under the open immersion is empty. Thus the
pullback of its vanishing ideal is the unit ideal: at every point of C the ideal's stalk is
the full local ring. The point ideal on the smooth ambient curve is invertible, and its dual
represents O(P). Pullback commutes with this dual, so the pulled-back invertible module is
the dual of the unit module, hence isomorphic to the unit module. Passing to Picard classes
gives the identity. This argument applies individually to every omitted closed point; when
there are no such points the assertion has no instances. -/
theorem Scheme.Hom.pic_restriction_boundary_trivial
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    (P : closedPoints c.Z) (hP : P.val ∉ Set.range c.i.base) :
    Scheme.Pic.mapHom c.i (@Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P) = 1  := by
  classical
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  let : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 c.g
    exact hsm
  let J : c.Z.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{P.val}, P.property⟩
  have hJ : J.IsInvertible :=
    Scheme.isInvertible_vanishingIdeal_of_isClosed c.g P.property
  have ht : J.comap c.i = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    apply SetLike.coe_injective
    change c.i.base ⁻¹' (J.support : Set c.Z) = ∅
    simp only [J, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    ext x
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact hP ⟨x, hx⟩
  have hJ' : (J.comap c.i).IsInvertible := by
    rw [ht]
    exact Scheme.IdealSheafData.isInvertible_top
  have := hJ.isInvertible_toModules
  have := hJ'.isInvertible_toModules
  obtain ⟨e⟩ := hJ.nonempty_pullback_toModules_iso c.i hJ'
  have hmap : Scheme.Pic.mapHom c.i (Scheme.Pic.ofIsInvertible J.toModules) =
      Scheme.Pic.ofIsInvertible (J.comap c.i).toModules := by
    apply Scheme.Pic.eq_iff_nonempty_iso.2
    exact ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Scheme.Modules.pullback c.i).mapIso (Scheme.Pic.ofIsInvertibleIso _) ≪≫ e ≪≫
      (Scheme.Pic.ofIsInvertibleIso _).symm⟩
  change Scheme.Pic.mapHom c.i (Scheme.Pic.ofIsInvertible J.toModulesᵛ) = 1
  rw [Scheme.Pic.ofIsInvertible_dual, map_inv, hmap]
  have htop : Scheme.Pic.ofIsInvertible (J.comap c.i).toModules = 1 := by
    have := (Scheme.IdealSheafData.isInvertible_top (X := C)).isInvertible_toModules
    have e := eqToIso (congrArg Scheme.IdealSheafData.toModules ht)
    exact (Scheme.Pic.ofIsInvertible_eq_of_iso e).trans
      Scheme.Pic.ofIsInvertible_toModules_top
  rw [htop, inv_one]

end AlgebraicGeometry
