/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Pullback of representable sheaves

Let `G : C ⥤ D` be a continuous functor between subcanonical sites and let `L` be a left
adjoint of the pushforward of sheaves along `G`. Then `L` sends the sheaf represented by `c : C`
to the sheaf represented by `G c`, naturally in `c`
(`CategoryTheory.Adjunction.uliftYonedaCompIso`): for every sheaf `F` on `D`,
`Hom(L(y c), F) ≃ Hom(y c, G_* F) ≃ F(G c) ≃ Hom(y (G c), F)`.

This is used to show that the inverse image of the sheaf of sections of an étale scheme is the
sheaf of sections of its base change.
-/

@[expose] public section

universe w v u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D] {G : C ⥤ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [G.IsContinuous J K]
  [J.Subcanonical] [K.Subcanonical] {L : Sheaf J (Type (max v w)) ⥤ Sheaf K (Type (max v w))}
  (adj : L ⊣ G.sheafPushforwardContinuous (Type (max v w)) J K)

/-- The universal element of `L (y c)` over `G c`: the unit of the adjunction at `y c`. -/
noncomputable def uliftYonedaElem (c : C) :
    (L.obj (J.uliftYoneda.{w}.obj c)).obj.obj (Opposite.op (G.obj c)) :=
  J.uliftYonedaEquiv (adj.unit.app (J.uliftYoneda.{w}.obj c))

/-- The comparison morphism `y (G c) ⟶ L (y c)`. -/
noncomputable def uliftYonedaCompHom (c : C) :
    K.uliftYoneda.{w}.obj (G.obj c) ⟶ L.obj (J.uliftYoneda.{w}.obj c) :=
  K.uliftYonedaEquiv.symm (adj.uliftYonedaElem c)

/-- Composing the comparison morphism with `g : L (y c) ⟶ F` corresponds, under the Yoneda
bijections, to the adjoint of `g`. -/
lemma uliftYonedaEquiv_uliftYonedaCompHom_comp (c : C) {F : Sheaf K (Type (max v w))}
    (g : L.obj (J.uliftYoneda.{w}.obj c) ⟶ F) :
    K.uliftYonedaEquiv (adj.uliftYonedaCompHom c ≫ g) =
      J.uliftYonedaEquiv (adj.homEquiv _ _ g) := by
  rw [GrothendieckTopology.uliftYonedaEquiv_comp, uliftYonedaCompHom, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit, GrothendieckTopology.uliftYonedaEquiv_comp]
  rfl

/-- The comparison morphism `y (G c) ⟶ L (y c)` is an isomorphism: composition with it is the
bijection `Hom(L (y c), F) ≃ Hom(y c, G_* F) ≃ F(G c) ≃ Hom(y (G c), F)`. -/
instance (c : C) : IsIso (adj.uliftYonedaCompHom c) := by
  refine isIso_of_coyoneda_map_bijective _ fun F ↦ ?_
  have : (fun g : L.obj (J.uliftYoneda.{w}.obj c) ⟶ F ↦ adj.uliftYonedaCompHom c ≫ g) =
      K.uliftYonedaEquiv.symm ∘ J.uliftYonedaEquiv ∘ adj.homEquiv _ _ := by
    ext1 g
    rw [Function.comp_apply, Function.comp_apply, ← uliftYonedaEquiv_uliftYonedaCompHom_comp,
      Equiv.symm_apply_apply]
  rw [this]
  exact K.uliftYonedaEquiv.symm.bijective.comp
    (J.uliftYonedaEquiv.bijective.comp (adj.homEquiv _ _).bijective)

/-- The comparison morphisms are natural in `c`. -/
lemma uliftYonedaCompHom_naturality {c c' : C} (f : c ⟶ c') :
    K.uliftYoneda.{w}.map (G.map f) ≫ adj.uliftYonedaCompHom c' =
      adj.uliftYonedaCompHom c ≫ L.map (J.uliftYoneda.{w}.map f) := by
  apply K.uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_uliftYonedaCompHom_comp, ← GrothendieckTopology.uliftYonedaEquiv_naturality,
    uliftYonedaCompHom, Equiv.apply_symm_apply, uliftYonedaElem,
    Adjunction.homEquiv_unit]
  have h1 : adj.unit.app (J.uliftYoneda.{w}.obj c) ≫
      (G.sheafPushforwardContinuous (Type (max v w)) J K).map (L.map (J.uliftYoneda.{w}.map f)) =
      J.uliftYoneda.{w}.map f ≫ adj.unit.app (J.uliftYoneda.{w}.obj c') :=
    adj.unit_naturality (J.uliftYoneda.{w}.map f)
  rw [h1, ← GrothendieckTopology.uliftYonedaEquiv_naturality]
  rfl

/-- **The left adjoint of the pushforward sends representable sheaves to representable
sheaves**: `L (y c) ≅ y (G c)`, naturally in `c`. -/
noncomputable def uliftYonedaCompIso :
    J.uliftYoneda.{w} ⋙ L ≅ G ⋙ K.uliftYoneda.{w} :=
  (NatIso.ofComponents (fun c ↦ asIso (adj.uliftYonedaCompHom c))
    fun f ↦ adj.uliftYonedaCompHom_naturality f).symm

end CategoryTheory.Adjunction
