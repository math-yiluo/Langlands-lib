/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying

import all WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardAdic

/-! # Formal quotients by a second ideal

Source: Stacks Project, Tag 088A, the systems F_n/K^e F_n.
(blueprint: lem-weil-pbc-formal-second-ideal-quotient-supported).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The second-ideal quotient system is annihilated by the closed thickening's ideal.
Source: Stacks Project, Tag 088A, construction of G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-quotient-supported).

Proof: At I-level n the system is M_n/K^(e+1)M_n, so the cokernel quotient
construction makes multiplication by the recursively defined K-power zero.
The kernel ideal of the closed immersion V(K^(e+1)) into X is K^(e+1).
On each affine open the section images of its associated ideal module and of the
recursively constructed ideal power are both the ideal K(U)^(e+1). Hence their
products with the quotient module have the same zero image there. The quotient
and ideal products are quasi-coherent. Equality on the affine basis therefore
makes the product inclusion zero globally, and its monomorphism proves the
product object is zero. This establishes the asserted annihilation at every n;
no algebraization or compatibility of algebraization choices is required. -/
theorem formalSecondIdealQuotient_supported
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I) (e : ℕ) :
    ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (K ^ (e + 1)).subschemeι.ker.toModulesι
      (((M.obj ⋙ formalCompletionFunctor K).flip.obj (op e)).obj (op n))) := by
  intro n
  rw [Scheme.IdealSheafData.ker_subschemeι]
  obtain ⟨p, hp⟩ := power_inclusion_iso K (e + 1) (Nat.succ_pos e)
  obtain ⟨d, _⟩ := product_inclusion_iso _ _ p hp
    (formalModuleQuotient K (e + 1) (M.obj.obj (op n)))
  exact d.isZero_iff.mp
    (idealModuleProduct_quotient_zero (Scheme.idealSheafPower K.toModulesι (e + 1)).2)

end AlgebraicGeometry
