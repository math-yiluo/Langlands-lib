/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalEtale
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierSourceComparison

/-! # Comparison pullback of the normalized Cartier class -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

private theorem ext_iso_precomp {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {X Y Z : C} (e : X ≅ Y) (κ : Ext X Z 2) :
    (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp κ (zero_add 2)) (zero_add 2) = κ := by
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    e.hom_inv_id, Ext.mk₀_id_comp]

namespace AlgebraicGeometry.ProEtale

/-- Apply exact comparison inverse image to the uniquely normalized ordinary class
and identify its supported source by the specified mate.
Source: blueprint lemma-cycle-class-cartier-divisor, opening comparison paragraph
(blueprint: lemma-cycle-class-cartier-divisor). -/
def geoCartierCanonicalClass (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) : GeoCartierClass A n hA i :=
  (Ext.mk₀ (asIso (geoCartierSourceComparison A i)).inv).comp
    ((Etale.geoCartierEtaleClass A n hn hA i hI hZ).mapExactFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z)) (zero_add 2)

/-- The comparison equation holds for the actual supported-source mate.
Source: blueprint lemma-cycle-class-cartier-divisor, opening comparison paragraph
(blueprint: def-sfb-geo-cartier-canonical-class).
Proof: compose the inverse source mate in the construction with its forward map.
Associativity of Yoneda composition and the inverse identities cancel them. -/
theorem geoCartierCanonicalClass_comparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    (Ext.mk₀ (geoCartierSourceComparison A i)).comp
        (geoCartierCanonicalClass A n hn hA i hI hZ) (zero_add 2) =
      (Etale.geoCartierEtaleClass A n hn hA i hI hZ).mapExactFunctor
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z) := by
  exact ext_iso_precomp (asIso (geoCartierSourceComparison A i)) _

end AlgebraicGeometry.ProEtale
