/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.CategoryTheory.Adjunction.UnitProjection
public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal

/-!
# The unit projection map of a sheafified monoidal adjunction

Let `adj : L ⊣ R` be an adjunction between monoidal categories with `R` lax monoidal and
preserving sheafification. The induced adjunction `Sheaf.adjunction J adj` between the sheafified
postcomposition with `L` and the postcomposition with `R` has lax monoidal right adjoint
`sheafCompose J R` for the sheafified tensor products. Its unit projection map
`K ⊗ R_* 𝟙 ⟶ R_* (L_* K)` (`CategoryTheory.Adjunction.unitProjection`) is an isomorphism as soon
as the one of `adj` is (`CategoryTheory.isIso_sheafAdjunction_unitProjection`): up to
morphisms inverted by sheafification it is the objectwise unit projection map of `adj` on the
underlying presheaves.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory

omit [BraidedCategory A] in
/-- The unit `ε : 𝟙_ ⟶ (𝟙_ : Sheaf J A).obj` of the lax monoidal functor `sheafToPresheaf` is
inverted by sheafification. -/
lemma GrothendieckTopology.W_ε_sheafToPresheaf : J.W (ε (sheafToPresheaf J A)) := by
  have h : ε (sheafToPresheaf J A) = (sheafificationAdjunction J A).unit.app _ ≫
      (sheafToPresheaf J A).map (η (presheafToSheaf J A)) :=
    (sheafificationAdjunction J A).homEquiv_unit _ _ _
  rw [h]
  exact J.W.comp_mem _ _ (J.W_adj_unit_app _ _)
    ((J.W_sheafToPresheaf_map_iff_isIso _).2 inferInstance)

omit [BraidedCategory A] in
/-- The comparison `μ : P.obj ⊗ Q.obj ⟶ (P ⊗ Q).obj` of the lax monoidal functor
`sheafToPresheaf` is inverted by sheafification. -/
lemma GrothendieckTopology.W_μ_sheafToPresheaf (P Q : Sheaf J A) :
    J.W (μ (sheafToPresheaf J A) P Q) := by
  have h : μ (sheafToPresheaf J A) P Q = (sheafificationAdjunction J A).unit.app _ ≫
      (sheafToPresheaf J A).map (δ (presheafToSheaf J A) _ _ ≫
        ((sheafificationAdjunction J A).counit.app P ⊗ₘ
          (sheafificationAdjunction J A).counit.app Q)) :=
    (sheafificationAdjunction J A).homEquiv_unit _ _ _
  rw [h]
  exact J.W.comp_mem _ _ (J.W_adj_unit_app _ _)
    ((J.W_sheafToPresheaf_map_iff_isIso _).2 inferInstance)

section Adjunction

variable {B' : Type*} [Category B'] [MonoidalCategory B'] [BraidedCategory B']
  [(J.W (A := B')).IsMonoidal] [HasWeakSheafify J B'] {L : B' ⥤ A} {R : A ⥤ B'} (adj : L ⊣ R)
  [J.HasSheafCompose R] [R.LaxMonoidal] [J.PreservesSheafification R]

omit [BraidedCategory A] [BraidedCategory B'] in
/-- **The unit projection map of a sheafified adjunction.** If the unit projection map
`X ⊗ R 𝟙 ⟶ R (L X)` of `adj : L ⊣ R` is an isomorphism and `R` preserves sheafification, the
unit projection map `K ⊗ R_* 𝟙 ⟶ R_* (L_* K)` of the adjunction `Sheaf.adjunction J adj` is an
isomorphism. -/
theorem isIso_sheafAdjunction_unitProjection [∀ X, IsIso (adj.unitProjection X)]
    (K : Sheaf J B') : IsIso ((Sheaf.adjunction J adj).unitProjection K) := by
  have hθ := sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app J R
  have key := (adj.whiskerRight Cᵒᵖ).unitProjection_comp_map_comp_app (Sheaf.adjunction J adj)
    (sheafToPresheafCompWhiskeringRightIsoSheafCompose J R).hom K (toSheafify J (K.obj ⋙ L)) (by
      rw [hθ]
      erw [Category.comp_id]
      exact (Sheaf.adjunction_unit_app_hom J adj K).symm)
  rw [hθ, hθ] at key
  erw [Category.comp_id, Category.comp_id] at key
  have h₁ : J.W ((adj.whiskerRight Cᵒᵖ).unitProjection ((sheafToPresheaf J B').obj K) ≫
      ((Functor.whiskeringRight _ _ _).obj R).map (toSheafify J (K.obj ⋙ L))) :=
    J.W.comp_mem _ _ ((J.W_iff _).2 inferInstance)
      (GrothendieckTopology.PreservesSheafification.le (J := J) (F := R) _ (J.W_toSheafify _))
  rw [key] at h₁
  have h₂ : J.W ((sheafToPresheaf J B').obj K ◁ ((Functor.whiskeringRight _ _ _).obj R).map
      (ε (sheafToPresheaf J A))) :=
    MorphismProperty.IsMonoidal.whiskerLeft _ _
      (GrothendieckTopology.PreservesSheafification.le (J := J) (F := R) _
        (J.W_ε_sheafToPresheaf))
  have h₃ := J.W_μ_sheafToPresheaf K ((sheafCompose J R).obj (𝟙_ _))
  rw [← J.W_sheafToPresheaf_map_iff_isIso]
  rw [J.W_iff] at h₁ h₂ h₃ ⊢
  rw [Functor.map_comp, Functor.map_comp] at h₁
  have : IsIso ((presheafToSheaf J B').map (μ (sheafToPresheaf J B') K
      ((sheafCompose J R).obj (𝟙_ _))) ≫ (presheafToSheaf J B').map
        ((sheafToPresheaf J B').map ((Sheaf.adjunction J adj).unitProjection K))) :=
    IsIso.of_isIso_comp_left ((presheafToSheaf J B').map ((sheafToPresheaf J B').obj K ◁
      ((Functor.whiskeringRight _ _ _).obj R).map (ε (sheafToPresheaf J A)))) _
  exact IsIso.of_isIso_comp_left ((presheafToSheaf J B').map (μ (sheafToPresheaf J B') K
    ((sheafCompose J R).obj (𝟙_ _)))) _

end Adjunction

end CategoryTheory
