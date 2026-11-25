/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor

/-!
# Twisting algebras with invertible structure morphism

Let `F : C ⥤ C` be an endofunctor and `α : F ≅ F` an automorphism of `F`. An algebra
`(a, Φ : F a ≅ a)` with invertible structure morphism can be *twisted* by `α`: the twist is
`(a, α_a ≫ Φ)`. This is an automorphism of the category `IsoAlgebra F`
(`CategoryTheory.Endofunctor.IsoAlgebra.twistEquivalence`), which does not change the
underlying objects and morphisms.

For the Weil sheaves of `WeilConjectures.WeilSheaf.Category`, multiplication by a unit `b` of the
coefficients is an automorphism of the Frobenius pullback, and the twist by it is the constant
Weil twist `F ⊗ 𝓑_b`.

A transport `mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G` along `e : L ⋙ G ≅ F ⋙ L` commutes
with twists by automorphisms `α` of `F` and `β` of `G` which correspond under `L`
(`CategoryTheory.Endofunctor.IsoAlgebra.twistCompMapOfNatIsoIso`), and so does its total right
derived functor (`CategoryTheory.Endofunctor.IsoAlgebra.mapDerivedCategoryTwistCompIso`).

## Main declarations

- `CategoryTheory.Endofunctor.IsoAlgebra.twist`: the twist by an automorphism of `F`.
- `CategoryTheory.Endofunctor.IsoAlgebra.twistEquivalence`: the twist is an equivalence.
- `CategoryTheory.Endofunctor.IsoAlgebra.twistCompMapOfNatIsoIso`: transports commute with
  twists.
- `CategoryTheory.Endofunctor.IsoAlgebra.mapDerivedCategoryTwistCompIso`: so do their total right
  derived functors.
- `CategoryTheory.Endofunctor.IsoAlgebra.mapDerivedCategoryTwistCompRightDerivedFunctorIso` and
  `CategoryTheory.Endofunctor.IsoAlgebra.mapDerivedCategoryTwistCompMapDerivedCategoryIso`: the
  total right derived functor of an additive functor, and the functor induced by an exact
  functor, commute with twists if the functor does.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

section Twist

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

@[ext]
lemma hom_ext {K K' : IsoAlgebra F} {φ ψ : K ⟶ K'} (h : φ.hom.f = ψ.hom.f) : φ = ψ :=
  ObjectProperty.hom_ext _ (Algebra.Hom.ext h)

/-- An isomorphism of algebras with invertible structure morphism, from an isomorphism of the
underlying objects compatible with the structure isomorphisms. -/
def isoMk {K K' : IsoAlgebra F} (e : K.carrier ≅ K'.carrier)
    (w : F.map e.hom ≫ K'.obj.str = K.obj.str ≫ e.hom) : K ≅ K' :=
  ObjectProperty.isoMk _ (Algebra.isoMk e w)

@[simp]
lemma isoMk_hom_hom_f {K K' : IsoAlgebra F} (e : K.carrier ≅ K'.carrier)
    (w : F.map e.hom ≫ K'.obj.str = K.obj.str ≫ e.hom) : (isoMk e w).hom.hom.f = e.hom :=
  rfl

@[simp]
lemma isoMk_inv_hom_f {K K' : IsoAlgebra F} (e : K.carrier ≅ K'.carrier)
    (w : F.map e.hom ≫ K'.obj.str = K.obj.str ≫ e.hom) : (isoMk e w).inv.hom.f = e.inv :=
  rfl

/-- The *twist* of algebras with invertible structure morphism by an automorphism `α` of `F`:
an algebra `(a, Φ)` is sent to `(a, α_a ≫ Φ)`, and morphisms are unchanged. It is the transport
`mapOfNatIso` along the identity functor and `α`. -/
noncomputable def twist (α : F ≅ F) : IsoAlgebra F ⥤ IsoAlgebra F :=
  mapOfNatIso (L := 𝟭 C) (F.leftUnitor ≪≫ α ≪≫ F.rightUnitor.symm)

@[simp]
lemma twist_obj_carrier (α : F ≅ F) (K : IsoAlgebra F) :
    ((twist α).obj K).carrier = K.carrier :=
  rfl

@[simp]
lemma twist_obj_obj_str (α : F ≅ F) (K : IsoAlgebra F) :
    ((twist α).obj K).obj.str = α.hom.app K.carrier ≫ K.obj.str := by
  change (F.leftUnitor ≪≫ α ≪≫ F.rightUnitor.symm).hom.app K.carrier ≫ K.obj.str = _
  simp

@[simp]
lemma twist_map_hom_f (α : F ≅ F) {K K' : IsoAlgebra F} (φ : K ⟶ K') :
    ((twist α).map φ).hom.f = φ.hom.f :=
  rfl

/-- The twist does not change underlying objects. -/
noncomputable def twistCompForgetIso (α : F ≅ F) : twist α ⋙ forget F ≅ forget F :=
  Iso.refl _

/-- Twisting by `α` and then by `β` is twisting by `β ≪≫ α`. -/
noncomputable def twistCompTwistIso (α β : F ≅ F) : twist α ⋙ twist β ≅ twist (β ≪≫ α) :=
  NatIso.ofComponents (fun K ↦ isoMk (Iso.refl _) (by simp)) fun φ ↦ by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The twist by the identity is the identity. -/
noncomputable def twistReflIso : twist (Iso.refl F) ≅ 𝟭 (IsoAlgebra F) :=
  NatIso.ofComponents (fun K ↦ isoMk (Iso.refl _) (by simp)) fun φ ↦ by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The twist by an automorphism is an equivalence, with inverse the twist by the inverse
automorphism. -/
@[simps functor inverse]
noncomputable def twistEquivalence (α : F ≅ F) : IsoAlgebra F ≌ IsoAlgebra F where
  functor := twist α
  inverse := twist α.symm
  unitIso := NatIso.ofComponents (fun K ↦ isoMk (Iso.refl _) (by simp)) fun φ ↦ by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  counitIso := NatIso.ofComponents (fun K ↦ isoMk (Iso.refl _) (by simp)) fun φ ↦ by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  functor_unitIso_comp K := by
    ext
    exact Category.id_comp _

instance (α : F ≅ F) : (twist α).IsEquivalence :=
  (twistEquivalence α).isEquivalence_functor

section Map

variable {D : Type u'} [Category.{v'} D] {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)
  (α : F ≅ F) (β : G ≅ G)

lemma mapOfNatIso_obj_obj_str (K : IsoAlgebra F) :
    ((mapOfNatIso e).obj K).obj.str = e.hom.app K.carrier ≫ L.map K.obj.str :=
  rfl

/-- **Transports commute with twists.** If automorphisms `α` of `F` and `β` of `G` correspond
under `e : L ⋙ G ≅ F ⋙ L`, then `twist α ⋙ mapOfNatIso e ≅ mapOfNatIso e ⋙ twist β`, with
identity components on underlying objects. -/
noncomputable def twistCompMapOfNatIsoIso
    (h : ∀ a, β.hom.app (L.obj a) ≫ e.hom.app a = e.hom.app a ≫ L.map (α.hom.app a)) :
    twist α ⋙ mapOfNatIso e ≅ mapOfNatIso e ⋙ twist β :=
  NatIso.ofComponents (fun K ↦ isoMk (Iso.refl _) (by
    simp only [Functor.comp_obj, Iso.refl_hom, twist_obj_obj_str, mapOfNatIso_obj_obj_str]
    change G.map (𝟙 (L.obj K.carrier)) ≫ β.hom.app (L.obj K.carrier) ≫ e.hom.app K.carrier ≫
        L.map K.obj.str =
      (e.hom.app K.carrier ≫ L.map (α.hom.app K.carrier ≫ K.obj.str)) ≫ 𝟙 (L.obj K.carrier)
    simp [reassoc_of% (h K.carrier)])) fun φ ↦ by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end Map

end Twist

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L) (α : F ≅ F) (β : G ≅ G)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]

instance : (twist α).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

/-- **Right derived functors commute with twists.** If an additive functor
`Φ : IsoAlgebra F ⥤ IsoAlgebra G` commutes with the twists by `α` and `β`, so does its total
right derived functor. -/
noncomputable def mapDerivedCategoryTwistCompRightDerivedFunctorIso
    (Φ : IsoAlgebra F ⥤ IsoAlgebra G) [Φ.Additive] (e : twist α ⋙ Φ ≅ Φ ⋙ twist β) :
    (twist α).mapDerivedCategory ⋙ Φ.rightDerivedFunctor ≅
      Φ.rightDerivedFunctor ⋙ (twist β).mapDerivedCategory :=
  Functor.isoWhiskerRight (twist α).rightDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    (Functor.rightDerivedFunctorCompIso (twist α) Φ).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso Φ (twist β)

/-- **Exact functors commute with twists on derived categories.** If an exact functor
`Φ : IsoAlgebra F ⥤ IsoAlgebra G` commutes with the twists by `α` and `β`, so does the functor
it induces on derived categories. -/
noncomputable def mapDerivedCategoryTwistCompMapDerivedCategoryIso
    (Φ : IsoAlgebra F ⥤ IsoAlgebra G) [Φ.Additive] [PreservesFiniteLimits Φ]
    [PreservesFiniteColimits Φ] (e : twist α ⋙ Φ ≅ Φ ⋙ twist β) :
    (twist α).mapDerivedCategory ⋙ Φ.mapDerivedCategory ≅
      Φ.mapDerivedCategory ⋙ (twist β).mapDerivedCategory :=
  have := IsoAlgebra.preservesFiniteLimits_mapOfNatIso (F.leftUnitor ≪≫ α ≪≫ F.rightUnitor.symm)
  have := IsoAlgebra.preservesFiniteColimits_mapOfNatIso (F.leftUnitor ≪≫ α ≪≫ F.rightUnitor.symm)
  have := IsoAlgebra.preservesFiniteLimits_mapOfNatIso (G.leftUnitor ≪≫ β ≪≫ G.rightUnitor.symm)
  have := IsoAlgebra.preservesFiniteColimits_mapOfNatIso (G.leftUnitor ≪≫ β ≪≫ G.rightUnitor.symm)
  Functor.mapDerivedCategoryCompIso _ _ ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- **Right derived transports commute with twists.** If automorphisms `α` of `F` and `β` of
`G` correspond under `e : L ⋙ G ≅ F ⋙ L`, the total right derived functor of the transport
`mapOfNatIso e` commutes with the twists, which are exact and act levelwise:

```
D(IsoAlgebra F) --R(mapOfNatIso e)--> D(IsoAlgebra G)
      |                                    |
   twist α                              twist β
      v                                    v
D(IsoAlgebra F) --R(mapOfNatIso e)--> D(IsoAlgebra G)
```
-/
noncomputable def mapDerivedCategoryTwistCompIso
    (h : ∀ a, β.hom.app (L.obj a) ≫ e.hom.app a = e.hom.app a ≫ L.map (α.hom.app a)) :
    (twist α).mapDerivedCategory ⋙ (mapOfNatIso e).rightDerivedFunctor ≅
      (mapOfNatIso e).rightDerivedFunctor ⋙ (twist β).mapDerivedCategory :=
  mapDerivedCategoryTwistCompRightDerivedFunctorIso α β (mapOfNatIso e)
    (twistCompMapOfNatIsoIso e α β h)

end Derived

end CategoryTheory.Endofunctor.IsoAlgebra
