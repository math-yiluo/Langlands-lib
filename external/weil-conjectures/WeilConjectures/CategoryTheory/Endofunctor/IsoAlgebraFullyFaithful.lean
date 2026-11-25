/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Transport of algebras along a fully faithful functor

For a functor `L : C ⥤ D` with a commutation isomorphism `e : L ⋙ G ≅ F ⋙ L`, the transport
`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G` is fully
faithful as soon as `L` is: a morphism `L a ⟶ L a'` compatible with the transported structure
isomorphisms comes from a unique morphism `a ⟶ a'`, which is compatible with the structure
isomorphisms since `L` is faithful.

As an application, an endofunctor `T` of a category which is fully faithful and satisfies
`T ⋙ T ≅ T` is isomorphic to the identity
(`CategoryTheory.Functor.FullyFaithful.isoIdOfCompSelfIso`).
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

/-- The transport of algebras along a fully faithful functor is fully faithful. -/
noncomputable def fullyFaithfulMapOfNatIso (hL : L.FullyFaithful) :
    (mapOfNatIso e).FullyFaithful where
  preimage {K K'} g := ObjectProperty.homMk
    { f := hL.preimage g.hom.f
      h := by
        apply hL.map_injective
        have hg := g.hom.h
        have hn := e.hom.naturality (hL.preimage g.hom.f)
        simp only [Functor.comp_map, Functor.FullyFaithful.map_preimage] at hn
        change G.map g.hom.f ≫ (e.app K'.carrier ≪≫ L.mapIso K'.str).hom =
          (e.app K.carrier ≪≫ L.mapIso K.str).hom ≫ g.hom.f at hg
        simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hg
        have hn' : e.hom.app K.carrier ≫ L.map (F.map (hL.preimage g.hom.f)) =
            G.map g.hom.f ≫ e.hom.app K'.carrier := hn.symm
        rw [Functor.map_comp, Functor.map_comp, Functor.FullyFaithful.map_preimage,
          ← cancel_epi (e.hom.app K.carrier), ← Category.assoc, hn', Category.assoc]
        rw [str_hom, str_hom] at hg
        rw [hg, Category.assoc] }
  map_preimage g := ObjectProperty.hom_ext _ (Algebra.Hom.ext (hL.map_preimage g.hom.f))
  preimage_map f := ObjectProperty.hom_ext _ (Algebra.Hom.ext (hL.preimage_map f.hom.f))

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type u} [Category.{v} C] {T : C ⥤ C}

/-- A fully faithful endofunctor `T` with `T ⋙ T ≅ T` is isomorphic to the identity: whiskering
on the right by `T` is fully faithful, and it carries `T ≅ 𝟭` to `T ⋙ T ≅ T`. -/
noncomputable def isoIdOfCompSelfIso (hT : T.FullyFaithful) (μ : T ⋙ T ≅ T) : T ≅ 𝟭 C :=
  (hT.whiskeringRight C).preimageIso (μ ≪≫ (Functor.leftUnitor T).symm)

end CategoryTheory.Functor.FullyFaithful
