/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.HigherImageCohomologySquareRawMap
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
/-- Composing the hom of an isomorphism built by `Coyoneda.ext` with a morphism out of
its target is computed by the given inverse correspondence `q`.
Source: Stacks Project, Tag 001P (Yoneda lemma).
(blueprint: lem-sf-higher-image-cohomology-square-represented-generator-transport). -/
theorem CategoryTheory.Coyoneda.ext_hom_comp {C : Type*} [Category C] (X Y : C)
    (p : ∀ {Z : C}, (X ⟶ Z) → (Y ⟶ Z))
    (q : ∀ {Z : C}, (Y ⟶ Z) → (X ⟶ Z))
    (h₁ : ∀ {Z : C} (f : X ⟶ Z), q (p f) = f) (h₂ : ∀ {Z : C} (f : Y ⟶ Z), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Y ⟶ Z) (g : Z ⟶ Z'), q (f ≫ g) = q f ≫ g) {Z : C} (g : Y ⟶ Z) :
    (Coyoneda.ext X Y p q h₁ h₂ n).hom ≫ g = q g := by
  have : (Coyoneda.ext X Y p q h₁ h₂ n).hom = q (𝟙 Y) := rfl
  rw [this, ← n, Category.id_comp]

namespace AlgebraicGeometry.Etale
/-- Naturality of the free-representable generator across inverse image.
This is the represented-generator step in the derived-mate calculation.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: lem-sf-higher-image-cohomology-square-represented-generator-transport). -/
theorem higherImageCohomologySquare_represented_generator_transport
    {S T : Scheme.{u}} (a : T ⟶ S) (U : S.Etale)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : (abelianComparisonFree T).obj (a.Etale.obj U) ⟶ G) :
    freeRepresentableHomEquiv T (a.Etale.obj U) G x =
      freeRepresentableHomEquiv S U (((a)_*[AddCommGrpCat.{u + 1}]).obj G)
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).homEquiv _ _
          ((abelianFreeRepresentablePullbackIso a U).hom ≫ x)) := by
  unfold abelianFreeRepresentablePullbackIso
  rw [CategoryTheory.Coyoneda.ext_hom_comp]
  · simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply, Equiv.symm_symm]
    rfl
  all_goals intros; simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
end AlgebraicGeometry.Etale
