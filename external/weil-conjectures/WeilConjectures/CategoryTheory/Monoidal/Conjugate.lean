/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Conjugates of monoidal natural transformations between monoidal left adjoints

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be monoidal adjunctions whose left adjoints are strong
monoidal. The conjugate `L₂ ⟶ L₁` of a monoidal natural transformation `R₁ ⟶ R₂` is monoidal for
the lax structures of the left adjoints (`CategoryTheory.isMonoidal_conjugateEquiv_symm`): this
is the oplax statement `CategoryTheory.conjugateEquiv_symm_app_tensor_comp_δ`, read through the
inverse comparison maps.

Similarly, if `L₁` and `L₂` are strong monoidal left adjoints of the same lax monoidal functor
`R`, with `adj₁` monoidal and the unit of `adj₂` monoidal, the comparison isomorphism
`L₁ ≅ L₂` given by uniqueness of left adjoints is monoidal
(`CategoryTheory.isMonoidal_leftAdjointUniq_hom`). This applies when `adj₂` comes from an
equivalence whose unit is given by explicit monoidal isomorphisms.

These statements are kept in a separate file to avoid rebuilding the many files importing
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation`; their natural home is
the Mathlib file `Mathlib.CategoryTheory.Monoidal.NaturalTransformation`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type*} [Category C] [MonoidalCategory C] {D : Type*} [Category D]
  [MonoidalCategory D]

section Conjugate

variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.Monoidal] [L₂.Monoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- The conjugate `(conjugateEquiv adj₁ adj₂).symm e : L₂ ⟶ L₁` of a monoidal natural
transformation `e : R₁ ⟶ R₂` between the right adjoints of two monoidal adjunctions with
strong monoidal left adjoints is monoidal. -/
lemma isMonoidal_conjugateEquiv_symm (e : R₁ ⟶ R₂) [NatTrans.IsMonoidal e] :
    NatTrans.IsMonoidal ((conjugateEquiv adj₁ adj₂).symm e) where
  unit := by
    rw [← cancel_mono (η L₁), Category.assoc, conjugateEquiv_symm_app_unit_comp_η,
      Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  tensor X Y := by
    rw [← cancel_mono (δ L₁ X Y), Category.assoc, conjugateEquiv_symm_app_tensor_comp_δ,
      Functor.Monoidal.μ_δ_assoc, Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

end Conjugate

section LeftAdjointUniq

variable {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (adj₁ : L₁ ⊣ R) (adj₂ : L₂ ⊣ R)
  [L₁.Monoidal] [L₂.Monoidal] [R.LaxMonoidal] [adj₁.IsMonoidal] [NatTrans.IsMonoidal adj₂.unit]

/-- The comparison `L₁ ≅ L₂` of two strong monoidal left adjoints of a lax monoidal functor `R`
is monoidal, if the first adjunction is monoidal and the unit of the second one is monoidal. -/
lemma isMonoidal_leftAdjointUniq_hom :
    NatTrans.IsMonoidal (adj₁.leftAdjointUniq adj₂).hom where
  unit := by
    rw [← cancel_epi (η L₁), Functor.Monoidal.η_ε_assoc]
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit,
      Functor.map_comp, ← Category.assoc, Adjunction.unit_app_unit_comp_map_η]
    have := NatTrans.IsMonoidal.unit (τ := adj₂.unit)
    simp only [Functor.LaxMonoidal.id_ε, Functor.LaxMonoidal.comp_ε, Category.id_comp] at this
    exact this
  tensor X Y := by
    rw [← cancel_epi (δ L₁ X Y), Functor.Monoidal.δ_μ_assoc]
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit,
      Functor.map_comp, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_app_tensor_comp_map_δ, Category.assoc, ← μ_natural_assoc,
      tensorHom_comp_tensorHom_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
      Adjunction.unit_leftAdjointUniq_hom_app]
    have := NatTrans.IsMonoidal.tensor (τ := adj₂.unit) X Y
    simp only [Functor.LaxMonoidal.id_μ, Functor.LaxMonoidal.comp_μ, Category.id_comp,
      Functor.id_obj, Functor.comp_obj] at this
    exact this

end LeftAdjointUniq

end CategoryTheory
