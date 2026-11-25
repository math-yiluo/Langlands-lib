/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Right unitality using only the unit tensor square -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- Right unitality needs the tensor square only at the chosen representative
and the coefficient unit, rather than on every pair of complexes.
Source: Stacks Project, Tag 07A4
(blueprint: lem-pur-scalar-right-unit-at-representative).
Proof: postcompose by the monic computation counit at X. Substitute the unit
normalization in its tensor with that counit. Naturality of the derived tensor
comparison moves the localized source unit into the representative tensor square.
Its normalization and ordinary right unitality give the localized right unitor.
Naturality of the counit then gives the other side. Cancel the monomorphism.
Only the displayed tensor square at X and the unit is used.
-/
theorem rightUnit_at_representative
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (Q : C ⥤ D) [Q.LaxMonoidal] (R : E ⥤ H) [R.LaxMonoidal]
    (F : C ⥤ E) (S : D ⥤ H)
    (r : Q ⋙ S ⟶ F ⋙ R)
    (δ : ∀ X Y : D, S.obj (X ⊗ Y) ⟶ S.obj X ⊗ S.obj Y)
    (η : S.obj (𝟙_ D) ⟶ 𝟙_ H)
    (hδ : ∀ X {Y Z : D} (f : Y ⟶ Z),
      S.map (X ◁ f) ≫ δ X Z = δ X Y ≫ (S.obj X ◁ S.map f))
    (X : C) (c : F.obj (X ⊗ 𝟙_ C) ⟶ F.obj X ⊗ F.obj (𝟙_ C))
    (e : F.obj (𝟙_ C) ⟶ 𝟙_ E)
    (hc : c ≫ (F.obj X ◁ e) ≫ (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (ht : δ (Q.obj X) (Q.obj (𝟙_ C)) ≫ (r.app X ⊗ₘ r.app (𝟙_ C)) ≫
        Functor.LaxMonoidal.μ R (F.obj X) (F.obj (𝟙_ C)) =
      S.map (Functor.LaxMonoidal.μ Q X (𝟙_ C)) ≫ r.app (X ⊗ 𝟙_ C) ≫
        R.map c)
    (hu : S.map (Functor.LaxMonoidal.ε Q) ≫ r.app (𝟙_ C) ≫
      R.map e = η ≫ Functor.LaxMonoidal.ε R)
    [Mono (r.app X)] :
    δ (Q.obj X) (𝟙_ D) ≫ (S.obj (Q.obj X) ◁ η) ≫ (ρ_ (S.obj (Q.obj X))).hom =
      S.map (ρ_ (Q.obj X)).hom := by
  apply (cancel_mono (r.app X)).1
  have h := congrArg (fun z ↦ δ (Q.obj X) (𝟙_ D) ≫
    (r.app X ⊗ₘ z) ≫ Functor.LaxMonoidal.μ R (F.obj X) (𝟙_ E) ≫
      R.map (ρ_ (F.obj X)).hom) hu
  have hleft : δ (Q.obj X) (𝟙_ D) ≫
      (r.app X ⊗ₘ (S.map (Functor.LaxMonoidal.ε Q) ≫ r.app (𝟙_ C) ≫
        R.map e)) ≫
      Functor.LaxMonoidal.μ R (F.obj X) (𝟙_ E) ≫ R.map (ρ_ (F.obj X)).hom =
      S.map (ρ_ (Q.obj X)).hom ≫ r.app X := by
    simp only [tensorHom_def, whiskerLeft_comp, Category.assoc, Functor.comp_obj]
    rw [← whisker_exchange_assoc]
    rw [← reassoc_of% (hδ (Q.obj X) (Functor.LaxMonoidal.ε Q))]
    rw [Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [← tensorHom_def_assoc, reassoc_of% ht]
    simp only [← R.map_comp]
    rw [hc]
    have hn := r.naturality (ρ_ X).hom
    dsimp only [Functor.comp_map] at hn
    rw [← hn]
    simp only [Functor.LaxMonoidal.right_unitality, Functor.map_comp, Category.assoc]
  have hright : δ (Q.obj X) (𝟙_ D) ≫
      (r.app X ⊗ₘ (η ≫ Functor.LaxMonoidal.ε R)) ≫
      Functor.LaxMonoidal.μ R (F.obj X) (𝟙_ E) ≫ R.map (ρ_ (F.obj X)).hom =
      (δ (Q.obj X) (𝟙_ D) ≫ (S.obj (Q.obj X) ◁ η) ≫
        (ρ_ (S.obj (Q.obj X))).hom) ≫ r.app X := by
    simp only [tensorHom_def, whiskerLeft_comp, Category.assoc, Functor.comp_obj]
    rw [← Functor.LaxMonoidal.right_unitality]
    rw [← whisker_exchange_assoc, rightUnitor_naturality]
  exact hright.symm.trans (h.symm.trans hleft)

end CategoryTheory
