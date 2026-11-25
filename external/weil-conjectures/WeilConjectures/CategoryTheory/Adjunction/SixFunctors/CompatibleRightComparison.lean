/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The right comparison determined by a left adjunction square

Source: Mathlib's mates correspondence and Stacks Project, Tag 0037.
(blueprint: new-lem-sf-adjunction-compatible-right-comparison)
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
namespace CategoryTheory.Adjunction
open CategoryTheory CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- A right comparison with its two adjunction equations. Invertibility of this
comparison is unnecessary for the mate calculation.
Source: Stacks Project, Tag 0037; Mathlib's `mateEquiv`.
(blueprint: new-lem-sf-adjunction-compatible-right-comparison) -/
structure CompatibleRightComparison (adj : F ⊣ G) (adj' : F' ⊣ G')
    (q : F ⋙ V ≅ U ⋙ F') where
  hom : G ⋙ U ⟶ V ⋙ G'
  unit (K : A) :
    U.map (adj.unit.app K) ≫ hom.app (F.obj K) ≫ G'.map (q.hom.app K) =
      adj'.unit.app (U.obj K)
  counit (K : B) :
    q.hom.app (G.obj K) ≫ F'.map (hom.app K) ≫ adj'.counit.app (V.obj K) =
      V.map (adj.counit.app K)

/-- Construct the right comparison as the mate of the inverse left comparison.
The unit and counit equations follow from Mathlib's two mate identities and
cancellation of the inverse left comparison.
Source: Stacks Project, Tag 0037; `unit_mateEquiv` and `mateEquiv_counit`.
(blueprint: new-lem-sf-adjunction-compatible-right-comparison) -/
def compatibleRightComparison (adj : F ⊣ G) (adj' : F' ⊣ G')
    (q : F ⋙ V ≅ U ⋙ F') : CompatibleRightComparison adj adj' q where
  hom := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ q.inv))
  unit K := by
    have h := unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ q.inv) K
    change U.map (adj.unit.app K) ≫ _ =
      adj'.unit.app (U.obj K) ≫ G'.map (q.inv.app K) at h
    rw [← Category.assoc, h, Category.assoc, ← G'.map_comp]
    simp
  counit K := by
    have h := mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ q.inv) K
    change F'.map _ ≫ adj'.counit.app (V.obj K) =
      q.inv.app (G.obj K) ≫ V.map (adj.counit.app K) at h
    rw [h, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Adjunction
