/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# The fibre of a constant sheaf at a point

For a point `Φ` of a site `(C, J)` and `M : A`, the fibre of the constant presheaf at `M` is
`M` (`CategoryTheory.GrothendieckTopology.Point.presheafFiberConstIso`): it is the colimit
of a constant functor over the connected category of elements of the fibre functor. When
`A` is concrete and `J.W` is the class of locally bijective morphisms, the fibre functor
inverts the sheafification maps, so the fibre of the constant sheaf at `M` is `M` as well
(`CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso`). Both isomorphisms
are natural in `M`; the second one is the natural isomorphism
`CategoryTheory.GrothendieckTopology.Point.constantSheafCompSheafFiberIso` from
`constantSheaf J A ⋙ Φ.sheafFiber` to the identity.

-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

instance : IsConnected (Φ.fiber.Elements)ᵒᵖ :=
  IsFiltered.isConnected _

/-- The fibre of the constant presheaf at `M` is `M`: the colimit of a constant functor over
the connected category of elements of the fibre functor. -/
noncomputable def presheafFiberConstIso (M : A) :
    Φ.presheafFiber.obj ((Functor.const Cᵒᵖ).obj M) ≅ M :=
  colimit.isoColimitCocone ⟨_, isColimitConstCocone (Φ.fiber.Elements)ᵒᵖ M⟩

@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberConstIso_hom (M : A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x ((Functor.const Cᵒᵖ).obj M) ≫ (Φ.presheafFiberConstIso M).hom =
      𝟙 M :=
  colimit.isoColimitCocone_ι_hom _ _

/-- Naturality of `CategoryTheory.GrothendieckTopology.Point.presheafFiberConstIso` in `M`:
```
  Φ.presheafFiber.obj (const M) --presheafFiberConstIso M--> M
              |                                               |
  Φ.presheafFiber.map (const.map f)                           f
              v                                               v
  Φ.presheafFiber.obj (const N) --presheafFiberConstIso N--> N
```
-/
@[reassoc (attr := simp)]
lemma presheafFiberConstIso_hom_naturality {M N : A} (f : M ⟶ N) :
    Φ.presheafFiber.map ((Functor.const Cᵒᵖ).map f) ≫ (Φ.presheafFiberConstIso N).hom =
      (Φ.presheafFiberConstIso M).hom ≫ f := by
  refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
  simp [Φ.toPresheafFiber_naturality_assoc]

variable [HasWeakSheafify J A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [J.WEqualsLocallyBijective A] [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (CategoryTheory.forget A)] [LocallySmall.{w} C]

/-- The fibre functor inverts the sheafification map of the constant presheaf. -/
instance isIso_presheafFiber_map_toSheafify_const (M : A) :
    IsIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))) :=
  Φ.W_isInvertedBy_presheafFiber' _ (J.W_toSheafify _)

/-- **The fibre of a constant sheaf at a point is its value**: `(M_C)_Φ ≅ M`. -/
noncomputable def sheafFiberConstantSheafIso (M : A) :
    Φ.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M :=
  (asIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)))).symm ≪≫
    Φ.presheafFiberConstIso M

/-- Naturality of `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso`
in `M`:
```
  Φ.sheafFiber.obj (M_C) --sheafFiberConstantSheafIso M--> M
            |                                              |
  Φ.sheafFiber.map (f_C)                                   f
            v                                              v
  Φ.sheafFiber.obj (N_C) --sheafFiberConstantSheafIso N--> N
```
where `f_C = (constantSheaf J A).map f`. -/
@[reassoc (attr := simp)]
lemma sheafFiberConstantSheafIso_hom_naturality {M N : A} (f : M ⟶ N) :
    Φ.sheafFiber.map ((constantSheaf J A).map f) ≫ (Φ.sheafFiberConstantSheafIso N).hom =
      (Φ.sheafFiberConstantSheafIso M).hom ≫ f := by
  dsimp only [sheafFiberConstantSheafIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, sheafFiber,
    constantSheaf, Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_map]
  rw [Category.assoc, IsIso.eq_inv_comp, ← Φ.presheafFiber.map_comp_assoc,
    ← CategoryTheory.sheafifyMap.eq_1, ← CategoryTheory.toSheafify_naturality,
    Functor.map_comp_assoc, IsIso.hom_inv_id_assoc, presheafFiberConstIso_hom_naturality]

/-- Under the isomorphisms `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso`,
the fibre of `(constantSheaf J A).map f` is `f`. -/
lemma sheafFiber_map_constantSheaf_map {M N : A} (f : M ⟶ N) :
    Φ.sheafFiber.map ((constantSheaf J A).map f) =
      (Φ.sheafFiberConstantSheafIso M).hom ≫ f ≫ (Φ.sheafFiberConstantSheafIso N).inv := by
  rw [← Φ.sheafFiberConstantSheafIso_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

variable (J A) in
/-- **The fibre of the constant sheaf functor is the identity**: `constantSheaf J A ⋙ Φ.sheafFiber
≅ 𝟭 A`, with components `CategoryTheory.GrothendieckTopology.Point.sheafFiberConstantSheafIso`. -/
noncomputable def constantSheafCompSheafFiberIso : constantSheaf J A ⋙ Φ.sheafFiber ≅ 𝟭 A :=
  NatIso.ofComponents Φ.sheafFiberConstantSheafIso Φ.sheafFiberConstantSheafIso_hom_naturality

@[simp]
lemma constantSheafCompSheafFiberIso_app (M : A) :
    (Φ.constantSheafCompSheafFiberIso J A).app M = Φ.sheafFiberConstantSheafIso M :=
  rfl

end CategoryTheory.GrothendieckTopology.Point
