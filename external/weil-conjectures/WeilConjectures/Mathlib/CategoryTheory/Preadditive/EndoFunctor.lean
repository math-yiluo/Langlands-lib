/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# The abelian structure on algebras of an endofunctor

Let `F : C ⥤ C` be an additive endofunctor of an abelian category. If `F` preserves finite
colimits, then `Algebra F` is abelian: kernels and cokernels are computed on the underlying
objects, and the coimage–image comparison of a morphism of algebras is that of the underlying
morphism.

The algebras with invertible structure morphism contain a zero object, are closed under
kernels if `F` preserves kernels, and are closed under cokernels if `F` preserves cokernels.
Hence if `F` is exact, `IsoAlgebra F` is abelian, and its forgetful functor to `C` is exact.

## Main results

- `CategoryTheory.Endofunctor.Algebra.abelian`: `Algebra F` is abelian.
- `CategoryTheory.Endofunctor.IsoAlgebra.abelian`: `IsoAlgebra F` is abelian.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.Endofunctor

open Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C]

namespace Algebra

variable {F : C ⥤ C}

section Abelian

variable (F) [Abelian C] [F.Additive] [PreservesFiniteColimits F]

instance {X Y : Algebra F} (φ : X ⟶ Y) : IsIso (Abelian.coimageImageComparison φ) := by
  have := Abelian.PreservesCoimageImageComparison.iso (forget F) φ
  rw [← isIso_iff_of_reflects_iso _ (forget F), Arrow.isIso_iff_isIso_of_isIso this.hom]
  exact inferInstanceAs (IsIso (Abelian.coimageImageComparison φ.f))

/-- The category of algebras of an additive endofunctor of an abelian category preserving
finite colimits is abelian. -/
instance abelian : Abelian (Algebra F) :=
  Abelian.ofCoimageImageComparisonIsIso

end Abelian

section IsIsoStr

open ZeroObject in
instance [HasZeroMorphisms C] [HasZeroObject C] [F.PreservesZeroMorphisms] :
    (IsIsoStr F).ContainsZero where
  exists_zero := by
    have h : IsZero (0 : C) := isZero_zero C
    refine ⟨⟨0, 0⟩, ⟨fun A ↦ ⟨⟨⟨⟨0, by simp⟩⟩, fun f ↦ Hom.ext (h.eq_of_src _ _)⟩⟩,
      fun A ↦ ⟨⟨⟨⟨0, by simp⟩⟩, fun f ↦ Hom.ext (h.eq_of_tgt _ _)⟩⟩⟩, ?_⟩
    exact (F.map_isZero h).isIso h _

variable [Preadditive C] [F.Additive]

instance [HasEqualizers C] [PreservesLimitsOfShape WalkingParallelPair F] :
    (IsIsoStr F).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (IsIsoStr F).prop_of_isLimit hk (by rintro (_ | _) <;> assumption)

instance [HasCoequalizers C] [PreservesColimitsOfShape WalkingParallelPair F] :
    (IsIsoStr F).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact (IsIsoStr F).prop_of_isColimit hk (by rintro (_ | _) <;> assumption)

end IsIsoStr

end Algebra

namespace IsoAlgebra

section Preadditive

variable {F : C ⥤ C} [Preadditive C] [F.Additive]

instance : Preadditive (IsoAlgebra F) :=
  inferInstanceAs (Preadditive (Algebra.IsIsoStr F).FullSubcategory)

instance : (ι F).Additive :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Additive

instance : (forget F).Additive :=
  inferInstanceAs (ι F ⋙ Algebra.forget F).Additive

instance : (ι F).Full :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Full

instance : (ι F).Faithful :=
  inferInstanceAs (Algebra.IsIsoStr F).ι.Faithful

instance : (forget F).ReflectsIsomorphisms :=
  inferInstanceAs (ι F ⋙ Algebra.forget F).ReflectsIsomorphisms

end Preadditive

variable (F : C ⥤ C) [Abelian C] [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- The category of algebras with invertible structure morphism of an exact additive
endofunctor of an abelian category is abelian. -/
instance abelian : Abelian (IsoAlgebra F) :=
  inferInstanceAs (Abelian (Algebra.IsIsoStr F).FullSubcategory)

instance {K L : IsoAlgebra F} (φ : K ⟶ L) : PreservesLimit (parallelPair φ 0) (ι F) :=
  (Algebra.IsIsoStr F).preservesKernels_ι φ

instance {K L : IsoAlgebra F} (φ : K ⟶ L) : PreservesColimit (parallelPair φ 0) (ι F) :=
  (Algebra.IsIsoStr F).preservesCokernels_ι φ

instance : PreservesFiniteLimits (ι F) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

instance : PreservesFiniteColimits (ι F) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

instance : PreservesFiniteLimits (forget F) :=
  comp_preservesFiniteLimits (ι F) (Algebra.forget F)

instance : PreservesFiniteColimits (forget F) :=
  comp_preservesFiniteColimits (ι F) (Algebra.forget F)

end IsoAlgebra

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive C] [Preadditive D] {F : C ⥤ C}
  {G : D ⥤ D} [F.Additive] [G.Additive] {L : C ⥤ D} [L.Additive]

/-- Transporting algebras along an additive functor `L`, compatibly with additive endofunctors
`F` and `G`, is additive: on morphisms it is `L.map`. -/
instance Algebra.additive_mapOfNatTrans (e : L ⋙ G ⟶ F ⋙ L) :
    (Algebra.mapOfNatTrans e).Additive where
  map_add := Algebra.Hom.ext L.map_add

/-- Transporting algebras with invertible structure morphism along an additive functor `L`,
compatibly with additive endofunctors `F` and `G`, is additive: on underlying morphisms it is
`L.map`. -/
instance IsoAlgebra.additive_mapOfNatIso (e : L ⋙ G ≅ F ⋙ L) :
    (IsoAlgebra.mapOfNatIso e).Additive where
  map_add := (IsoAlgebra.ι G).map_injective (Algebra.Hom.ext L.map_add)

/-- The transport `IsoAlgebra.mapOfNatIso e`, restricted to full subcategories `P` and `Q` of
algebras with invertible structure morphism, is additive. -/
lemma IsoAlgebra.additive_lift_mapOfNatIso {P : ObjectProperty (IsoAlgebra F)}
    {Q : ObjectProperty (IsoAlgebra G)} (e : L ⋙ G ≅ F ⋙ L)
    (h : ∀ K : P.FullSubcategory, Q ((IsoAlgebra.mapOfNatIso e).obj K.obj)) :
    (Q.lift (P.ι ⋙ IsoAlgebra.mapOfNatIso e) h).Additive :=
  inferInstance


end Map

end CategoryTheory.Endofunctor
