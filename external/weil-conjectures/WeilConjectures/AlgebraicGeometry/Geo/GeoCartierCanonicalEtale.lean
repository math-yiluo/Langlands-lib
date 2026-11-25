/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement

/-! # The uniquely normalized ordinary Cartier class -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The relative boundary determines the ordinary Cartier Ext class uniquely.
Source: blueprint lemma-cycle-class-cartier-divisor, (G1) and Kummer reduction
(blueprint: def-sfb-geo-cartier-canonical-etale). -/
def geoCartierEtaleClass (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine Z n A hA) 2 :=
  Classical.choose (supported_cartier_boundary_existsUnique Z n hn A hA hZ i hI)

/-- The canonical class has the specified boundary and is its only representative.
Source: blueprint lemma-cycle-class-cartier-divisor, construction and local lifts
(blueprint: def-sfb-geo-cartier-canonical-etale).
Proof: apply the existence-and-uniqueness specification of the ordinary supported
Kummer theorem. This fixes the Ext class itself, including its complementary
trivialization and positive sign; no representative extension is chosen. -/
theorem geoCartierEtaleClass_spec (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    SupportedKummerBoundary A n hA i hI hZ (geoCartierEtaleClass A n hn hA i hI hZ) ∧
      ∀ κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        (Scheme.finiteEtaleTateLine Z n A hA) 2,
        SupportedKummerBoundary A n hA i hI hZ κ →
          κ = geoCartierEtaleClass A n hn hA i hI hZ := by
  exact Classical.choose_spec
    (supported_cartier_boundary_existsUnique Z n hn A hA hZ i hI)

end AlgebraicGeometry.Etale
