/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-!
# Right derived functors on categories of algebras with invertible structure morphism

Let `F` be an additive autoequivalence of an abelian category `C` in which coproducts indexed
by `ℤ` exist and are exact. The free algebra functor `S ↦ ∐ₙ Fⁿ S` is then exact, so its right
adjoint, the forgetful functor `IsoAlgebra F ⥤ C`, preserves K-injective complexes
(`CategoryTheory.Endofunctor.IsoAlgebra.preservesKInjectiveComplexes_forget`).

Consequently the total right derived functor of a transported functor
`IsoAlgebra.mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G`, for `e : L ⋙ G ≅ F ⋙ L`, is computed
on underlying objects by the total right derived functor of `L`
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso`): forgetting
the algebra structures commutes with right derivation.

## Main results

- `CategoryTheory.Endofunctor.IsoAlgebra.Free.preservesHomology_functor`: the free algebra
  functor is exact.
- `CategoryTheory.Endofunctor.IsoAlgebra.preservesKInjectiveComplexes_forget`.
- `CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso`:
  `R(mapOfNatIso e) ⋙ For ≅ For ⋙ RL`.
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C] (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]

namespace Free

instance : (functor F).IsLeftAdjoint :=
  (adjunction F).isLeftAdjoint

instance : (functor F).Additive :=
  (adjunction F).left_adjoint_additive

/-- The free algebra functor `S ↦ ∐ₙ Fⁿ S` is exact: it is right exact as a left adjoint, and
it preserves monomorphisms since coproducts indexed by `ℤ` are exact. -/
instance preservesHomology_functor : (functor F).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

end Free

/-- The forgetful functor `IsoAlgebra F ⥤ C` preserves K-injective complexes, being right
adjoint to the exact free algebra functor. -/
instance preservesKInjectiveComplexes_forget : (forget F).PreservesKInjectiveComplexes :=
  (Free.adjunction F).preservesKInjectiveComplexes

variable {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]
  [Abelian.HasKInjectiveResolutions C]

/-- **Right derivation commutes with forgetting the algebra structures.** For an additive
functor `L : C ⥤ D` and `e : L ⋙ G ≅ F ⋙ L`, the total right derived functor of the transport
`mapOfNatIso e` of algebras is computed on underlying objects by the total right derived
functor of `L`: `R(mapOfNatIso e) ⋙ For ≅ For ⋙ RL`.

```
D(IsoAlgebra F) --R(mapOfNatIso e)--> D(IsoAlgebra G)
      |                                    |
     For                                  For
      v                                    v
     D(C) ---------------RL-------------> D(D)
```

Both sides are the total right derived functor of `For ⋙ L`, the forgetful functors being
exact and preserving K-injective complexes. -/
noncomputable def rightDerivedFunctorMapOfNatIsoCompForgetIso :
    (mapOfNatIso e).rightDerivedFunctor ⋙ (forget G).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ L.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (mapOfNatIso e) (forget G)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (mapOfNatIsoCompForgetIso e) ≪≫
    Functor.rightDerivedFunctorCompIso (forget F) L ≪≫
    Functor.isoWhiskerRight (forget F).rightDerivedFunctorIsoMapDerivedCategory
      L.rightDerivedFunctor

end CategoryTheory.Endofunctor.IsoAlgebra
