/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

/-!
# The tensor isomorphism of an arbitrary total left derived functor

Let `F : C ⥤ D` be a strong monoidal left adjoint between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms, but need not be exact (for
instance, extension of scalars along a quotient map of rings). The comparison
`LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of `CategoryTheory.Functor.leftDerivedTensorComparison` is an
isomorphism. This file records its components `LF(K ⊗ᴸ -) ≅ LF K ⊗ᴸ LF(-)` for a fixed `K`, and
transports them to any total left derived functor of `F`.

## Main definitions

- `CategoryTheory.Functor.leftDerivedTensorIso F K`: `LF(K ⊗ᴸ -) ≅ LF K ⊗ᴸ LF(-)`.
- `CategoryTheory.Functor.leftDerivedTensorIsoOfIsLeftDerivedFunctor`: the same isomorphism
  for any total left derived functor `L` of `F`.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint]
  [F.Monoidal]

/-- The isomorphism `LF(K ⊗ᴸ M) ≅ LF K ⊗ᴸ LF M`, natural in `M`, for a fixed `K`: a component of
the comparison `CategoryTheory.Functor.leftDerivedTensorComparison`. -/
noncomputable def leftDerivedTensorIso (K : DerivedCategory C) :
    (curriedTensor (DerivedCategory C)).obj K ⋙ F.leftDerivedFunctor ≅
      F.leftDerivedFunctor ⋙
        (curriedTensor (DerivedCategory D)).obj (F.leftDerivedFunctor.obj K) :=
  (asIso F.leftDerivedTensorComparison).app K

/-- The isomorphism `L(K ⊗ᴸ M) ≅ L K ⊗ᴸ L M`, natural in `M`, for any total left derived functor
`L` of `F` (`CategoryTheory.Functor.leftDerivedTensorIso` transported along the uniqueness of
left derived functors). Applying it to a left derived functor `L` constructed in another context
avoids comparing the instance arguments of the two constructions. -/
noncomputable def leftDerivedTensorIsoOfIsLeftDerivedFunctor
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (α : Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso C (.up ℤ))] (K : DerivedCategory C) :
    (curriedTensor (DerivedCategory C)).obj K ⋙ L ≅
      L ⋙ (curriedTensor (DerivedCategory D)).obj (L.obj K) :=
  let e : F.leftDerivedFunctor ≅ L := Functor.leftDerivedUnique _ _
    F.leftDerivedFunctorCounit α (HomotopyCategory.quasiIso C (.up ℤ))
  Functor.isoWhiskerLeft _ e.symm ≪≫ F.leftDerivedTensorIso K ≪≫
    Functor.isoWhiskerRight e _ ≪≫ Functor.isoWhiskerLeft L ((curriedTensor _).mapIso (e.app K))

end CategoryTheory.Functor
