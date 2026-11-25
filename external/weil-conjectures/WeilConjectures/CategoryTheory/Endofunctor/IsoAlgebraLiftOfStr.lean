/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-!
# Changing the structure isomorphisms of algebras

Let `F` and `G` be endofunctors of a category `C`. A family of isomorphisms
`φ K : G K ≅ K`, indexed by the algebras `K` of `IsoAlgebra F` and natural in the
morphisms of algebras, gives a functor `IsoAlgebra F ⥤ IsoAlgebra G`. It keeps the
underlying objects and morphisms and replaces the structure isomorphism of `K` by `φ K`.
For instance, the iterated structure isomorphisms `Fⁿ K ≅ K` give such a family for `G = Fⁿ`.

## Main definitions

- `CategoryTheory.Endofunctor.IsoAlgebra.liftOfStr`: the functor
  `IsoAlgebra F ⥤ IsoAlgebra G`, `K ↦ (K, φ K)`.

## Implementation notes

The functor and its compatibilities are stated for arbitrary `F` and `G`, so their proofs are
checked once. Proving them for a concrete pair of functors would make the kernel compare `F` with
`G`, which can be slow when they are large concrete functors.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {F : C ⥤ C} (G : C ⥤ C)
  (φ : ∀ K : IsoAlgebra F, G.obj K.carrier ≅ K.carrier)
  (hφ : ∀ {K K' : IsoAlgebra F} (f : K ⟶ K'), G.map f.hom.f ≫ (φ K').hom = (φ K).hom ≫ f.hom.f)

/-- The functor `IsoAlgebra F ⥤ IsoAlgebra G`, `K ↦ (K, φ K)`, keeping the underlying objects and
morphisms and replacing the structure isomorphism of `K` by a natural isomorphism
`φ K : G K ≅ K`. -/
def liftOfStr : IsoAlgebra F ⥤ IsoAlgebra G where
  obj K := mk K.carrier (φ K)
  map f := ObjectProperty.homMk
    { f := f.hom.f
      h := hφ f }

@[simp]
lemma liftOfStr_obj_carrier (K : IsoAlgebra F) :
    ((liftOfStr G φ hφ).obj K).carrier = K.carrier :=
  rfl

@[simp]
lemma liftOfStr_obj_str (K : IsoAlgebra F) : ((liftOfStr G φ hφ).obj K).str = φ K :=
  mk_str _ _

@[simp]
lemma liftOfStr_map_hom_f {K K' : IsoAlgebra F} (f : K ⟶ K') :
    ((liftOfStr G φ hφ).map f).hom.f = f.hom.f :=
  rfl

lemma liftOfStr_comp_forget : liftOfStr G φ hφ ⋙ forget G = forget F :=
  rfl


section Map

variable {D : Type u'} [Category.{v'} D] {G' : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G' ≅ G ⋙ L)

lemma liftOfStr_comp_mapOfNatIso_obj_str (K : IsoAlgebra F) :
    ((liftOfStr G φ hφ ⋙ mapOfNatIso e).obj K).str = e.app K.carrier ≪≫ L.mapIso (φ K) := by
  ext
  rfl

lemma liftOfStr_comp_mapOfNatIso_map_hom_f {K K' : IsoAlgebra F} (f : K ⟶ K') :
    ((liftOfStr G φ hφ ⋙ mapOfNatIso e).map f).hom.f = L.map f.hom.f :=
  rfl

end Map

instance additive_liftOfStr [Preadditive C] [F.Additive] [G.Additive] :
    (liftOfStr G φ hφ).Additive where

variable [Abelian C] [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

instance preservesFiniteLimits_liftOfStr : PreservesFiniteLimits (liftOfStr G φ hφ) := by
  have : PreservesFiniteLimits (liftOfStr G φ hφ ⋙ forget G) :=
    inferInstanceAs (PreservesFiniteLimits (forget F))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget G)

instance preservesFiniteColimits_liftOfStr : PreservesFiniteColimits (liftOfStr G φ hφ) := by
  have : PreservesFiniteColimits (liftOfStr G φ hφ ⋙ forget G) :=
    inferInstanceAs (PreservesFiniteColimits (forget F))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (forget G)

end CategoryTheory.Endofunctor.IsoAlgebra
