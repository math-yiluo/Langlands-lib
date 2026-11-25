/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec

import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.GenericProductLocalization
import WeilConjectures.AlgebraicGeometry.DescendModelLocalization

/-!
# Spreading an injective generic product map

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-spread-generic-product-embedding)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open AlgebraicGeometry

/-- Spread the generic product map with injectivity, coordinate idempotents, and
coordinate denominator clearing. This does not construct any domain factors.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9; the torsion,
idempotent and denominator arguments of `lem-weil-pbc-spread-generic-product-domains`.
(blueprint: lem-weil-pbc-spread-generic-product-embedding)

Proof: Set C to the reduction of B tensor A0. Its generic fibre is the specified product
of fields: tensor associativity identifies the unreduced generic fibres, and localization
commutes with taking the nilradical quotient. Since A0 is finite over the Noetherian
localization S0, C is finite over a Noetherian domain. The kernel of C to its generic
fibre is therefore finitely generated torsion. Choose annihilators of its generators
and invert their product; the resulting map into the generic product is injective.
Each coordinate idempotent in that product has a numerator in C and a nonzero denominator
in A0. Invert the product of these finitely many denominators too. The resulting map
contains all the coordinate idempotents. Every field element in every coordinate is
likewise a fraction with numerator in C and nonzero denominator in A0, since the map
on the generic fibre is surjective. These fractions remain available after shrinking.
For each element of A0 inverted above, integrality over S0 and a monic equation of
least degree give a nonzero constant coefficient in its principal ideal. Clear the
coefficients' c0 denominators and invert their product together with c0 in A. Base
change of A0 to this principal open is finite etale, a domain with fraction field K',
and its spectrum map remains surjective. It is small because it is a finite module
over a ring in Type u; transport it to a finite-module presentation in Type u. The
embedding and coordinate denominator identities transport as well. The algebra maps
to L j are the compositions through K', giving the stated scalar towers. When r = 0,
the generic ring is zero and torsion killing makes C zero; both coordinate assertions
are vacuous and the map from the zero ring is injective. -/
theorem exists_spread_generic_product_embedding
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (K' : Type (max u v)) [Field K'] [Algebra K K'] [Algebra A K']
    [IsScalarTower A K K']
    (r : ℕ) (L : Fin r → Type (max u v)) [∀ j, Field (L j)]
    [∀ j, Algebra K' (L j)]
    (hsplit :
      letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := K ⊗[A] B) (B := K')
      Nonempty ((((K ⊗[A] B) ⊗[K] K') ⧸
        nilradical ((K ⊗[A] B) ⊗[K] K')) ≃ₐ[K'] (∀ j, L j)))
    (c0 : A) (hc0 : c0 ≠ 0) (S0 : Subalgebra A K')
    [IsLocalization.Away c0 S0] (A0 : Subalgebra S0 K')
    [Module.Finite S0 A0] [Algebra.Etale S0 A0] [IsFractionRing A0 K']
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S0 A0)))) :
    ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
      (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A')
      (_ : IsDomain A') (_ : Algebra A' K'),
      c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
        Algebra.Etale (Localization.Away c) A' ∧ IsFractionRing A' K' ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))) ∧
        ∃ (_ : ∀ j, Algebra A' (L j)) (_ : ∀ j, IsScalarTower A' K' (L j)),
          letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A')
          ∃ f : ((B ⊗[A] A') ⧸ nilradical (B ⊗[A] A')) →ₐ[A'] (∀ j, L j),
            Function.Injective f ∧
            (∀ j, ∃ e, ∀ i, f e i = if i = j then 1 else 0) ∧
            (∀ j (z : L j), ∃ a : A', a ≠ 0 ∧
              ∃ x, algebraMap A' (L j) a * z = f x j) := by
  let : Algebra A A0 := Algebra.compHom A0 (algebraMap A S0)
  have : IsScalarTower A S0 A0 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A A0 K' := IsScalarTower.to₁₃₄ A S0 A0 K'
  have : IsNoetherianRing S0 :=
    IsLocalization.isNoetherianRing (Submonoid.powers c0) S0 inferInstance
  have : IsNoetherianRing A0 :=
    isNoetherian_of_tower S0 (inferInstance : IsNoetherian S0 A0)
  obtain ⟨t, ht, hlocal⟩ :=
    exists_generic_product_localization A B K K' A0 r L hsplit
  obtain ⟨s, hts, hs, c, A', instRing, instLocAlg, instAlg, instTower,
    instDomain, instFieldAlg, instModelAlg, instModelTower, instFracTower,
    instLocalization, hc, hfinite, hetale, hfrac, hsurj'⟩ :=
    exists_descend_model_localization A K' c0 hc0 S0 A0 hsurj t ht
  let := instRing
  let := instLocAlg
  let := instAlg
  let := instTower
  let := instDomain
  let := instFieldAlg
  let := instModelAlg
  let := instModelTower
  let := instFracTower
  let := instLocalization
  let := hfrac
  obtain ⟨instFactors, instFactorTowers, f, hf, hid, hden⟩ := hlocal s hts A'
  exact ⟨c, A', instRing, instLocAlg, instAlg, instTower, instDomain, instFieldAlg,
    hc, hfinite, hetale, hfrac, hsurj', instFactors, instFactorTowers, f, hf, hid, hden⟩

