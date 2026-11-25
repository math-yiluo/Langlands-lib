/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement

import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalChern
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionScalar
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionPullback
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionModulus

/-! # Canonical supported Cartier cycle classes

Source: blueprint lemma-cycle-class-cartier-divisor. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The canonical Cartier classes in the ordinary pro-etale module derived category,
with the Kummer Chern equation, arbitrary finite-coefficient extension, exponent
independence, and every Cartier-preserving base change. The auxiliary etale class fixes
the canonical construction by its relative torsor boundary; `geoCartierSourceComparison`
is the specified comparison mate, so no arbitrary source isomorphism occurs.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier, statement
and proof paragraphs 1--6; Stacks Project, Tag 03PL (blueprint: lemma-cycle-class-cartier-divisor).

Proof:
1. The ordinary supported Kummer theorem constructs the integral pole extension,
   its positive relative boundary and the scalar-reduced ordinary Cartier class.
   Its uniqueness clause fixes geoCartierEtaleClass without any arbitrary data.
2. The qcqs comparison mate is invertible for a closed immersion. Apply exact
   comparison inverse image to the ordinary class and precompose with its inverse.
   Cancellation proves the required comparison equation.
3. The unit compatibility of comparison carries the ordinary Kummer Chern equation
   to the pro-etale equation, retaining the same integral generator and dual ideal.
4. Derived coefficient transitivity, normalized on constants and pure root tensors,
   gives arbitrary coefficient compatibility for this canonical construction.
5. For exponent change, the Kummer sequence morphism (q, m/n, identity) carries the
   larger relative boundary to the smaller one. Boundary uniqueness, exact functoriality
   and associativity of Ext composition prove equality of the canonical classes.
6. Cartier-preserving pullback carries the pole extension and its normalized
   relative boundary to the pulled-back extension. Comparison respects the counit
   mate defining exchange and the normalized roots transport, giving base change.
-/
theorem exists_geoCartierCycleClass (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ c : GeoCartierClassFamily.{u} ℓ,
      (∀ (r : ℕ) (hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
        (hA : ((ℓ ^ r : ℕ) : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
        (hI : i.ker.IsInvertible) (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
        IsIso (geoCartierSourceComparison A i) ∧
        GeoCartierChernEquation A (ℓ ^ r) hA i hI hZ (c r hr A hA i hI hZ) ∧
        ∃ κ : Ext
          ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D))
          (Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA) 2,
          Etale.SupportedKummerBoundary A (ℓ ^ r) hA i hI hZ κ ∧
          (Ext.mk₀ (geoCartierSourceComparison A i)).comp (c r hr A hA i hI hZ)
              (zero_add 2) = κ.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)) ∧
      (∀ (r : ℕ) (hr : 0 < r) (A B : Type (u + 1))
        [CommRing A] [CommRing B] [Finite A] [Finite B]
        (hA : ((ℓ ^ r : ℕ) : A) = 0) (hB : ((ℓ ^ r : ℕ) : B) = 0) (φ : A →+* B)
        {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
        (hI : i.ker.IsInvertible) (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
        GeoCartierScalarCompatibility φ (ℓ ^ r) hA hB i
          (c r hr A hA i hI hZ) (c r hr B hB i hI hZ)) ∧
      GeoCartierBaseChange ℓ c ∧ GeoCartierExponentIndependence ℓ c := by
  let c : GeoCartierClassFamily.{u} ℓ := fun r _ A _ _ hA _ _ i _ hI hZ ↦
    geoCartierCanonicalClass A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro r hr A _ _ hA D Z i _ hI hZ
    refine ⟨inferInstance, geoCartierCanonicalClass_chern A (ℓ ^ r)
      (pow_pos hℓ.pos r) hA i hI hZ, ?_⟩
    exact ⟨Etale.geoCartierEtaleClass A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ,
      (Etale.geoCartierEtaleClass_spec A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ).1,
      geoCartierCanonicalClass_comparison A (ℓ ^ r) (pow_pos hℓ.pos r) hA i hI hZ⟩
  · intro r hr A B _ _ _ _ hA hB φ D Z i _ hI hZ
    exact geoCartierCanonicalClass_scalar A B (ℓ ^ r) (pow_pos hℓ.pos r) hA hB φ i hI hZ
  · unfold GeoCartierBaseChange
    intro r hr A _ _ hA
    exact geoCartierCanonicalClass_pullback A (ℓ ^ r) (pow_pos hℓ.pos r) hA
  · unfold GeoCartierExponentIndependence
    intro r s hr hs hrs A _ _ hA hA' D Z i _ hI hZ hZ'
    have hdiv : ℓ ^ r ∣ ℓ ^ s := pow_dvd_pow ℓ hrs
    let twists := Scheme.finiteEtaleTwistPullbackData A (ℓ ^ r) (pow_pos hℓ.pos r) hA
    obtain ⟨q, t, hq, ht, _⟩ := twists.laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (ℓ ^ s) (pow_pos hℓ.pos s) hdiv Z hZ'
    refine ⟨q, t 1, hq, ht, ?_⟩
    exact geoCartierCanonicalClass_modulus ℓ hℓ r s hr hs hrs A hA' hA
      i hI hZ' hZ q (t 1) hq ht

end AlgebraicGeometry.ProEtale
