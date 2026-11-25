/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Transported lax monoidal structures, conjugates of monoidal natural transformations

We show that the natural isomorphism along which a lax monoidal structure is transported
in `CategoryTheory.Functor.LaxMonoidal.transport` is a monoidal natural transformation.

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be monoidal adjunctions (`Adjunction.IsMonoidal`).
For a monoidal natural transformation `e : R₁ ⟶ R₂`, the conjugate transformation
`(conjugateEquiv adj₁ adj₂).symm e : L₂ ⟶ L₁` is compatible with the oplax monoidal structure
maps of the left adjoints (`CategoryTheory.conjugateEquiv_symm_app_unit_comp_η` and
`CategoryTheory.conjugateEquiv_symm_app_tensor_comp_δ`). Hence, if the right adjoints are
isomorphic via a monoidal natural isomorphism, the oplax structure maps of one left adjoint
are isomorphisms if and only if those of the other are (`CategoryTheory.isIso_η_of_conjugateIso`
and `CategoryTheory.isIso_δ_of_conjugateIso`). These results sit here rather than next to
`Adjunction.IsMonoidal` in `Mathlib/CategoryTheory/Monoidal/Functor.lean` because they are
about monoidal natural transformations, which are defined in this file's Mathlib counterpart.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Transporting a lax monoidal structure along a natural isomorphism of functors makes the
isomorphism a monoidal natural transformation. -/
lemma natTransIsMonoidal_of_transport {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) :
    letI := transport i
    i.hom.IsMonoidal := by
  let := transport i
  refine ⟨rfl, fun X Y ↦ ?_⟩
  simp [transport_μ, tensorHom_comp_tensorHom_assoc]

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- The conjugate `ẽ = (conjugateEquiv adj₁ adj₂).symm e : L₂ ⟶ L₁` of a monoidal natural
transformation `e : R₁ ⟶ R₂` between the right adjoints of two monoidal adjunctions is
compatible with the unit comparisons `η` of the oplax monoidal structures on the left
adjoints, i.e. the following diagram commutes:
```
  L₂(𝟙) ──ẽ.app 𝟙──▶ L₁(𝟙)
      ╲                │
   η L₂ ╲              │ η L₁
         ▼             ▼
                𝟙
```
-/
@[reassoc]
lemma conjugateEquiv_symm_app_unit_comp_η (e : R₁ ⟶ R₂) [NatTrans.IsMonoidal e] :
    ((conjugateEquiv adj₁ adj₂).symm e).app (𝟙_ C) ≫ η L₁ = η L₂ := by
  apply (adj₂.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← e.naturality,
    unit_app_unit_comp_map_η_assoc, NatTrans.IsMonoidal.unit,
    unit_app_unit_comp_map_η]

/-- The conjugate `ẽ = (conjugateEquiv adj₁ adj₂).symm e : L₂ ⟶ L₁` of a monoidal natural
transformation `e : R₁ ⟶ R₂` between the right adjoints of two monoidal adjunctions is
compatible with the tensor comparisons `δ` of the oplax monoidal structures on the left
adjoints, i.e. the following diagram commutes:
```
  L₂(X ⊗ Y) ──ẽ.app (X ⊗ Y)──▶ L₁(X ⊗ Y)
     │ δ L₂ X Y                     │ δ L₁ X Y
     ▼                              ▼
  L₂X ⊗ L₂Y ──ẽ.app X ⊗ ẽ.app Y──▶ L₁X ⊗ L₁Y
```
-/
@[reassoc]
lemma conjugateEquiv_symm_app_tensor_comp_δ (e : R₁ ⟶ R₂) [NatTrans.IsMonoidal e]
    (X Y : C) :
    ((conjugateEquiv adj₁ adj₂).symm e).app (X ⊗ Y) ≫ δ L₁ X Y =
      δ L₂ X Y ≫ (((conjugateEquiv adj₁ adj₂).symm e).app X ⊗ₘ
        ((conjugateEquiv adj₁ adj₂).symm e).app Y) := by
  apply (adj₂.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← e.naturality,
    unit_app_tensor_comp_map_δ_assoc, NatTrans.IsMonoidal.tensor,
    tensorHom_comp_tensorHom_assoc, unit_conjugateEquiv_symm adj₁ adj₂ e X,
    unit_conjugateEquiv_symm adj₁ adj₂ e Y, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural, unit_app_tensor_comp_map_δ_assoc]

include adj₁ adj₂ in
/-- If the right adjoints of two monoidal adjunctions are isomorphic via a monoidal
natural isomorphism and the unit comparison `η` of one left adjoint is an isomorphism,
then so is the other. -/
lemma isIso_η_of_conjugateIso (e : R₂ ≅ R₁) [NatTrans.IsMonoidal e.hom] [IsIso (η L₂)] :
    IsIso (η L₁) := by
  have : IsIso (((conjugateEquiv adj₁ adj₂).symm e.inv).app (𝟙_ C) ≫ η L₁) := by
    rw [conjugateEquiv_symm_app_unit_comp_η]
    infer_instance
  exact IsIso.of_isIso_comp_left (((conjugateEquiv adj₁ adj₂).symm e.inv).app (𝟙_ C)) _

include adj₁ adj₂ in
/-- If the right adjoints of two monoidal adjunctions are isomorphic via a monoidal
natural isomorphism and the tensor comparison `δ` of one left adjoint is an isomorphism,
then so is the other. -/
lemma isIso_δ_of_conjugateIso (e : R₂ ≅ R₁) [NatTrans.IsMonoidal e.hom] (X Y : C)
    [IsIso (δ L₂ X Y)] : IsIso (δ L₁ X Y) := by
  have : IsIso (((conjugateEquiv adj₁ adj₂).symm e.inv).app (X ⊗ Y) ≫ δ L₁ X Y) := by
    rw [conjugateEquiv_symm_app_tensor_comp_δ]
    infer_instance
  exact IsIso.of_isIso_comp_left (((conjugateEquiv adj₁ adj₂).symm e.inv).app (X ⊗ Y)) _

end CategoryTheory
