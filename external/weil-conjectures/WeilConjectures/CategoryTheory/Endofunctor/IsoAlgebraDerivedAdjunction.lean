/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedHomBijective

/-!
# Adjunctions between derived categories of algebras from underlying adjunctions

Let `F` and `G` be additive autoequivalences of Grothendieck abelian categories `C` and `D`, and
`L : D(IsoAlgebra F) ⥤ D(IsoAlgebra G)` a triangulated functor which is computed on underlying
objects by `L' : D(C) ⥤ D(D)`, through `c : L ⋙ For ≅ For ⋙ L'`. The morphisms of `D(IsoAlgebra F)`
are not determined by the underlying morphisms (the forgetful functor is not faithful), but they
are computed from them by the free resolution `Free(For K) ⟶ Free(For K) ⟶ K`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_freeDerivedWeilResolution`). Hence, for
`ε : L P ⟶ T`, the map `Hom(K, P) ⟶ Hom(L K, T)`, `g ↦ L g ≫ ε`, is bijective as soon as `L`
commutes with free objects on the shifts of `For K` (the free comparisons
`CategoryTheory.Adjunction.freeComparison` are isomorphisms) and the underlying maps
`Hom(For K[n], For P) ⟶ Hom(L' (For K[n]), For T)`, `f ↦ L' f ≫ c⁻¹ ≫ For ε`, are bijective
(`CategoryTheory.Endofunctor.IsoAlgebra.bijective_map_comp_of_bijective_forget`).

Applied to all objects, with `ε` the counit of a would-be adjunction, this produces adjunctions
between derived categories of algebras (for instance of Weil complexes) from adjunctions between
the underlying derived categories whose counit is compatible with the algebra structures
(`CategoryTheory.Adjunction.ofBijectiveCounit`).
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [IsGrothendieckAbelian.{w} D]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{w} D] [HasDerivedCategory.{w} (IsoAlgebra G)]

/-- **Bijectivity from the underlying morphisms.** Let `L : D(IsoAlgebra F) ⥤ D(IsoAlgebra G)` be
triangulated, `c : L ⋙ For ≅ For ⋙ L'` and `ε : L P ⟶ T`. If for every `n` the free comparison of
`L` at `(For K)[n]` is an isomorphism and `f ↦ L' f ≫ c⁻¹ ≫ For ε` is bijective on
`Hom((For K)[n], For P)`, then `g ↦ L g ≫ ε` is bijective on `Hom(K, P)`. -/
theorem bijective_map_comp_of_bijective_forget
    (L : DerivedCategory (IsoAlgebra F) ⥤ DerivedCategory (IsoAlgebra G)) [L.CommShift ℤ]
    [L.IsTriangulated] (L' : DerivedCategory C ⥤ DerivedCategory D)
    (c : L ⋙ (forget G).mapDerivedCategory ≅ (forget F).mapDerivedCategory ⋙ L')
    {P : DerivedCategory (IsoAlgebra F)} {T : DerivedCategory (IsoAlgebra G)}
    (ε : L.obj P ⟶ T) (K : DerivedCategory (IsoAlgebra F))
    (hc : ∀ n : ℤ, IsIso (Adjunction.freeComparison (freeWeilDerivedAdjunction F)
      (freeWeilDerivedAdjunction G) L L' c
      ((shiftFunctor _ n).obj ((forget F).mapDerivedCategory.obj K))))
    (h : ∀ n : ℤ, Function.Bijective fun f : (shiftFunctor _ n).obj
        ((forget F).mapDerivedCategory.obj K) ⟶ (forget F).mapDerivedCategory.obj P ↦
          L'.map f ≫ c.inv.app P ≫ (forget G).mapDerivedCategory.map ε) :
    Function.Bijective fun g : K ⟶ P ↦ L.map g ≫ ε := by
  refine bijective_map_comp_of_bijective_free F L ε K fun n ↦ ?_
  have := hc n
  refine (Adjunction.bijective_map_comp_iff_of_iso L ε
    (((Free.functor F).mapDerivedCategory.commShiftIso n).app _)).1 ?_
  exact (Adjunction.bijective_map_comp_free_iff (freeWeilDerivedAdjunction F)
    (freeWeilDerivedAdjunction G) L L' c _ ε).2 (h n)

end CategoryTheory.Endofunctor.IsoAlgebra
