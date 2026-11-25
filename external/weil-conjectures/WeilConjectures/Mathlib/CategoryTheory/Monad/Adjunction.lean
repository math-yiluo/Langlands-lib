/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Adjunctions whose left adjoint is isomorphic to the identity

If the left adjoint `L` of an adjunction `L ⊣ R` on a category `C` is isomorphic to the identity,
then so is `R`, and the unit and counit are isomorphisms.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {L R : C ⥤ C}

/-- If the left adjoint is isomorphic to the identity, the unit is an isomorphism. -/
lemma isIso_unit_of_iso_id (adj : L ⊣ R) (e : L ≅ 𝟭 C) : IsIso adj.unit :=
  adj.isIso_unit_of_iso (Functor.isoWhiskerRight e R ≪≫ R.leftUnitor ≪≫
    (adj.ofNatIsoLeft e).rightAdjointUniq Adjunction.id)

/-- If the left adjoint is isomorphic to the identity, the counit is an isomorphism. -/
lemma isIso_counit_of_iso_id (adj : L ⊣ R) (e : L ≅ 𝟭 C) : IsIso adj.counit :=
  adj.isIso_counit_of_iso (Functor.isoWhiskerLeft R e ≪≫ R.rightUnitor ≪≫
    (adj.ofNatIsoLeft e).rightAdjointUniq Adjunction.id)

/-- For adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` whose composite has invertible counit, and an
isomorphism `g : T ⟶ R₂ Z`, the composite `L₂ L₁ R₁ T ⟶ L₂ T ⟶ L₂ R₂ Z ⟶ Z` of the counits and
`g` is an isomorphism: by naturality it is `L₂ L₁ R₁ g` followed by the composite counit. -/
lemma isIso_map_counit_app_comp_map_comp_counit_app {C D E : Type*} [Category C] [Category D]
    [Category E] {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (h : IsIso (adj₁.comp adj₂).counit) (T : D) {Z : E} (g : T ⟶ R₂.obj Z)
    [IsIso g] : IsIso (L₂.map (adj₁.counit.app T) ≫ L₂.map g ≫ adj₂.counit.app Z) := by
  have e : L₂.map (adj₁.counit.app T) ≫ L₂.map g =
      L₂.map (L₁.map (R₁.map g)) ≫ L₂.map (adj₁.counit.app (R₂.obj Z)) := by
    rw [← L₂.map_comp, ← L₂.map_comp]
    simp
  have h' : IsIso ((adj₁.comp adj₂).counit.app Z) := inferInstance
  rw [Adjunction.comp_counit_app] at h'
  rw [← Category.assoc, e, Category.assoc]
  infer_instance

end CategoryTheory.Adjunction
