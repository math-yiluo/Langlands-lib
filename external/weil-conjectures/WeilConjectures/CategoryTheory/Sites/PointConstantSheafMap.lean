/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Fibres of morphisms out of constant sheaves

`CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso_inv_comp_sheafFiber_map`:
at a point `Φ` of a site with terminal object `T`, the fibre of a morphism `ψ : M_C ⟶ G` is,
through `(M_C)_Φ ≅ M`, the adjunct `M ⟶ Γ(T, G)` followed by the germ map `Γ(T, G) ⟶ G_Φ`.
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  [HasWeakSheafify J A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [J.WEqualsLocallyBijective A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget A)] [LocallySmall.{w} C]

/-- **The fibre of a morphism out of a constant sheaf** is its adjunct followed by the germ map
at the terminal object: `(M_C)_Φ ≅ M ⟶ G_Φ` is `M ⟶ Γ(T, G) ⟶ G_Φ`. -/
lemma sheafFiberConstantSheafIso_inv_comp_sheafFiber_map {T : C} (hT : IsTerminal T)
    (t : Φ.fiber.obj T) (M : A) (G : Sheaf J A) (ψ : (constantSheaf J A).obj M ⟶ G) :
    (Φ.sheafFiberConstantSheafIso M).inv ≫ Φ.sheafFiber.map ψ =
      (constantSheafAdj J A hT).homEquiv M G ψ ≫ Φ.toPresheafFiber T t G.obj := by
  rw [constantSheafAdj_homEquiv_apply, Category.assoc, ← Φ.toPresheafFiber_naturality]
  have h2 := Φ.toPresheafFiber_naturality (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))
    T t
  erw [← reassoc_of% h2]
  have h := Φ.toPresheafFiber_presheafFiberConstIso_hom M T t
  rw [← Iso.eq_comp_inv] at h
  erw [Category.id_comp] at h
  rw [h]
  simp only [sheafFiberConstantSheafIso, Iso.trans_inv, Iso.symm_inv, asIso_hom, Category.assoc]
  rfl

end CategoryTheory.GrothendieckTopology.Point
