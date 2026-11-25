/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# The distinguished triangle of a short exact sequence in `D⁺`

A short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in an abelian category gives a distinguished
triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[1]` in the bounded below derived category
(`CategoryTheory.ShortComplex.ShortExact.singleTrianglePlus` and
`CategoryTheory.ShortComplex.ShortExact.singleTrianglePlus_distinguished`): the lift of
Mathlib's `CategoryTheory.ShortComplex.ShortExact.singleTriangle` along the inclusion
`DerivedCategory.Plus C ⥤ DerivedCategory C`.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex.ShortExact

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] {E : ShortComplex C}

/-- The triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[1]` in the bounded below derived category
attached to a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`: the lift of
`CategoryTheory.ShortComplex.ShortExact.singleTriangle` along the inclusion
`DerivedCategory.Plus C ⥤ DerivedCategory C`. -/
noncomputable def singleTrianglePlus (hE : E.ShortExact) : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map E.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map E.g)
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimage
      (hE.singleδ ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj E.X₁)))

set_option backward.isDefEq.respectTransparency false in
/-- The triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[1]` attached to a short exact sequence is
distinguished in the bounded below derived category. -/
lemma singleTrianglePlus_distinguished (hE : E.ShortExact) :
    hE.singleTrianglePlus ∈ distTriang (DerivedCategory.Plus C) := by
  refine isomorphic_distinguished _ hE.singleTriangle_distinguished _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp [singleTrianglePlus, Functor.mapTriangle]
    rfl
  · simp [singleTrianglePlus, Functor.mapTriangle]
    rfl
  · simp only [Functor.mapTriangle, ObjectProperty.ι_obj, ObjectProperty.ι_map, Triangle.mk,
      singleTrianglePlus, ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_app,
      Functor.comp_obj, Iso.refl_hom, Functor.map_id, Category.comp_id, singleTriangle_mor₃,
      Category.id_comp]
    exact Category.comp_id _

/-- The distinguished triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[1]` of
`CategoryTheory.ShortComplex.ShortExact.singleTrianglePlus_distinguished`, written with
`CategoryTheory.Pretriangulated.Triangle.mk`, its objects and first two morphisms spelled out.
Use it over a concrete abelian category: there, identifying the objects and morphisms of
`hE.singleTrianglePlus` with those of `DerivedCategory.Plus.singleFunctor C 0` makes the kernel
unfold the derived category, while here the identification is checked once, over an abstract
`C`. The zero morphisms of `C` are an arbitrary instance, so that the lemma applies as it
stands to a short complex of sheaves, whose zero morphisms come from the full subcategory of
sheaves rather than from the abelian structure: comparing the two instances is expensive for
the kernel too. -/
lemma exists_mk_singleTrianglePlus_distinguished [Z : Limits.HasZeroMorphisms C]
    {E : ShortComplex C} (hE : E.ShortExact) :
    ∃ δ : (DerivedCategory.Plus.singleFunctor C 0).obj E.X₃ ⟶
        ((DerivedCategory.Plus.singleFunctor C 0).obj E.X₁)⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map E.f)
        ((DerivedCategory.Plus.singleFunctor C 0).map E.g) δ ∈
          distTriang (DerivedCategory.Plus C) := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  exact ⟨_, hE.singleTrianglePlus_distinguished⟩


/-- The image of a short exact sequence `E` under a functor `F : C ⥤ D` which factors as the
inclusion of `C` in degree `0` followed by a homological functor `G : D⁺(C) ⥤ D` is exact in
the middle: it is the image under `G` of the distinguished triangle of `E`.

The zero morphisms of `C` and of `D` are arbitrary instances, as in
`CategoryTheory.ShortComplex.ShortExact.exists_mk_singleTrianglePlus_distinguished`, so that the
lemma applies as it stands to sheaves. -/
lemma map_exact_of_isHomological [Z₀ : Limits.HasZeroMorphisms C] {E : ShortComplex C}
    (hE : E.ShortExact) {D : Type*} [Category* D] [Abelian D] [Z : Limits.HasZeroMorphisms D]
    (G : DerivedCategory.Plus C ⥤ D) [G.IsHomological] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : DerivedCategory.Plus.singleFunctor C 0 ⋙ G = F) :
    (E.map F).Exact := by
  obtain rfl : Z₀ = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  subst hF
  exact G.map_distinguished_exact _ hE.singleTrianglePlus_distinguished

end CategoryTheory.ShortComplex.ShortExact
