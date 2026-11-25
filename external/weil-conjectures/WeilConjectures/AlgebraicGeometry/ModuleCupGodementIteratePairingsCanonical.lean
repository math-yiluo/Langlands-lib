/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementBetaExists
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairingsFromBeta

/-! # Canonical recursively generated tensor pairing -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A natural tensor pairing for the concrete Godement construction, compatible with its
unit and multiplication. This is a type of data, not a choice of an unproved witness.
Source: Banerjee, arXiv:1004.1491, §1.1.4; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-iterate-pairings-canonical-exists) -/
structure ModuleCupGodementBeta (X : Scheme.{u}) where
  map : ∀ H K : X.Modules,
    moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
      moduleCup_godementObject X (H ⊗ K)

  naturality : ∀ (H K H' K' : X.Modules) (f : H ⟶ H') (g : K ⟶ K'),
    (moduleCup_godementMap X f ⊗ₘ moduleCup_godementMap X g) ≫ map H' K' =
      map H K ≫ moduleCup_godementMap X (f ⊗ₘ g)
  unit : ∀ H K : X.Modules,
    (moduleCup_godementUnit X H ⊗ₘ moduleCup_godementUnit X K) ≫ map H K =
      moduleCup_godementUnit X (H ⊗ K)
  multiply : ∀ H K : X.Modules,
    (moduleCup_godementMultiply X H ⊗ₘ moduleCup_godementMultiply X K) ≫ map H K =
      map (moduleCup_godementObject X H) (moduleCup_godementObject X K) ≫
        moduleCup_godementMap X (map H K) ≫ moduleCup_godementMultiply X (H ⊗ K)

/-- Canonical recursively generated tensor pairing.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-iterate-pairings-canonical-exists)
Proof: Project each factor T(H), T(K) to the skyscraper at x. Their tensor maps, by the tensor
universal property and the tensor map on stalks, into the skyscraper of the stalk of H tensor K.
Product universality defines beta. Naturality follows on pure tensors after each product
projection. Its unit law sends the tensor of two germs to the germ of their tensor. Its
multiplication law evaluates both outer germs at x and then tensors their inner x coordinates;
choosing a common representative neighbourhood verifies equality. Define p0 as identity and p(n+1)
as beta(T^n F,T^n G) followed by T(pn). Induct on n and split the insertion index into zero and
successor. The zero case uses beta.unit and naturality of the germ map; the successor case uses
beta.naturality, functoriality of T and the induction hypothesis. Empty products and zero sheaves
satisfy the same universal properties. -/
theorem moduleCup_godement_iterate_pairings_canonical_exists (X : Scheme.{u})
    (F G : X.Modules) :
    ∃ (β : ModuleCupGodementBeta X)
      (p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
        moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n),
      p 0 = 𝟙 (F ⊗ G) ∧
      (∀ n, p (n + 1) = β.map (moduleCup_godementIterate X F n)
        (moduleCup_godementIterate X G n) ≫ moduleCup_godementMap X (p n)) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        (moduleCup_godementInsert X F n i ⊗ₘ moduleCup_godementInsert X G n i) ≫
          p (n + 1) = p n ≫ moduleCup_godementInsert X (F ⊗ G) n i) := by
  obtain ⟨b, hbNat, hbUnit, hbMul⟩ := moduleCup_godement_beta_maps_exists X
  let β : ModuleCupGodementBeta X := ⟨b, hbNat, hbUnit, hbMul⟩
  obtain ⟨p, hp0, hprec, hpins⟩ :=
    moduleCup_godement_iterate_pairings_from_beta X F G b hbNat hbUnit
  exact ⟨β, p, hp0, hprec, hpins⟩

end
end AlgebraicGeometry.Scheme.Modules
