/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinates
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorStalkPairingExists
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorMapOfPairingExists

/-! # Existence of the coordinatewise Godement tensor map -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The coordinatewise tensor map exists, before checking its monad laws.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-tensor-coordinates-exists)
Proof: For two stalk elements choose representatives on a common neighbourhood and take the
stalk germ of their sectionwise tensor under `moduleCup_sectionTensor`. Restriction
compatibility makes this independent of representatives: intersect neighbourhoods on which
representatives agree, and use functoriality of the presheaf tensor and sheafification unit.
It is bilinear over the stalk ring by representing each scalar on a common neighbourhood.
For every point x, evaluate the two projections to its skyscrapers and apply this bilinear
map. On an open containing x these operations are bilinear over the ring of sections via the
ring germ, and on an open not containing x the skyscraper sections are zero. Thus tensor
universality gives a map of presheaves to that skyscraper. Sheafification adjunction extends
it uniquely to the sheaf tensor product. Product universality assembles these maps into b;
the construction gives exactly the two coordinate formulas. For an empty scheme this is the
unique map into the empty product. Zero inputs give the zero map by bilinearity. -/
theorem moduleCup_godement_tensor_coordinates_exists (X : Scheme.{u}) :
    ∃ b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K),
      ModuleCupGodementTensorCoordinates X b := by
  obtain ⟨t, ht⟩ := moduleCup_godement_tensor_stalk_pairing_exists X
  obtain ⟨b, hb⟩ := moduleCup_godement_tensor_map_of_pairing_exists X t ht
  refine ⟨b, t, ht, hb⟩

end
end AlgebraicGeometry.Scheme.Modules
