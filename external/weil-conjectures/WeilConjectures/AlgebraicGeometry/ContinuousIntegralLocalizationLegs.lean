/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization

/-! # Detecting the comparison of localization cocones on their unit legs -/

@[expose] public section

universe u v w x y
open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Maps of scalar telescopes are determined by the zeroth leg when the target
has invertible multiplication by the scalar.
Source: universal property of the localization telescope, Bhatt--Scholze 6.8.2.
(auxiliary; not a blueprint node).
Proof. Induct on the leg index. Cocone compatibility relates adjacent legs by ℓ;
centrality of integer multiplication moves ℓ to the target, where it cancels. -/
theorem integralLocalization_coconeLegs (ℓ : ℕ)
    {C : Type u} [Category.{v} C] [Preadditive C]
    {K : C} (c d : Cocone (Mod.smulSequence K ℓ))
    [IsIso (ℓ • 𝟙 d.pt)] (g : c.pt ⟶ d.pt)
    (hzero : c.ι.app 0 ≫ g = d.ι.app 0) :
    ∀ n, c.ι.app n ≫ g = d.ι.app n := by
  have central {P Q : C} (z : P ⟶ Q) :
      (ℓ • 𝟙 P) ≫ z = z ≫ (ℓ • 𝟙 Q) := by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.id_comp, Category.comp_id]
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      apply (cancel_mono (ℓ • 𝟙 d.pt)).1
      have hc' := c.w (homOfLE (Nat.le_add_right n 1))
      have hd' := d.w (homOfLE (Nat.le_add_right n 1))
      simp only [Nat.add_sub_cancel_left, pow_one] at hc' hd'
      calc
        (c.ι.app (n + 1) ≫ g) ≫ (ℓ • 𝟙 d.pt) =
            (ℓ • 𝟙 K) ≫ (c.ι.app (n + 1) ≫ g) := (central _).symm
        _ = c.ι.app n ≫ g := by rw [← Category.assoc, hc']
        _ = d.ι.app n := ih
        _ = (ℓ • 𝟙 K) ≫ d.ι.app (n + 1) := hd'.symm
        _ = d.ι.app (n + 1) ≫ (ℓ • 𝟙 d.pt) := central _

end AlgebraicGeometry.ProEtale.CondensedRing
