/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-!

# Extension of scalars of module objects preserves flatness

Let `C` be a closed symmetric monoidal abelian category and `φ : R ⟶ S` a morphism of
commutative algebra objects of `C`. For a flat `R`-module `N`, the `S`-module `S ⊗_R N` is flat
(`Mod.preservesFlat_extendScalars`): by the projection formula `Mod.projectionIso`, tensoring an
`S`-module `Q` with `S ⊗_R N` over `S` and restricting scalars to `R` is tensoring `Q`, with
scalars restricted to `R`, with `N` over `R` (`Mod.tensorRightExtendScalarsCompComapIso`).
Since restriction of scalars is exact and reflects isomorphisms, tensoring with `S ⊗_R N` is
exact.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- Restriction of scalars reflects isomorphisms: its composite with the forgetful functor is
the forgetful functor. -/
instance reflectsIsomorphisms_comap : (comap φ : Mod C S ⥤ Mod C R).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    have : IsIso ((forget S).map f) := inferInstanceAs (IsIso ((comap φ).map f).hom)
    exact isIso_of_reflects_iso f (forget S)

/-- **The projection formula as a natural isomorphism.** For an `R`-module `N`, tensoring with
`S ⊗_R N` over `S` followed by the restriction of scalars is the restriction of scalars followed
by tensoring with `N` over `R`. -/
noncomputable def tensorRightExtendScalarsCompComapIso (N : Mod C R) :
    tensorRight ((extendScalars φ).obj N) ⋙ comap φ ≅ comap φ ⋙ tensorRight N :=
  NatIso.ofComponents (fun Q ↦ (projectionIso φ Q N).symm) (fun {Q Q'} f ↦ by
    change (comap φ).map (f ▷ extendScalarsObj φ N) ≫ (projectionIso φ Q' N).inv =
      (projectionIso φ Q N).inv ≫ (comap φ).map f ▷ N
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, projectionIso_hom, projectionIso_hom,
      projectionHom_naturality])

/-- **Extension of scalars preserves flat objects**: for a flat `R`-module `N`, the `S`-module
`S ⊗_R N` is flat. -/
instance preservesFlat_extendScalars : (extendScalars φ).PreservesFlat where
  flat_obj {N} hN := by
    have := hN.tensorRight.preservesFiniteLimits
    have := hN.tensorRight.preservesFiniteColimits
    have : PreservesFiniteLimits (tensorRight ((extendScalars φ).obj N) ⋙ comap φ) :=
      preservesFiniteLimits_of_natIso (tensorRightExtendScalarsCompComapIso φ N).symm
    have : PreservesFiniteColimits (tensorRight ((extendScalars φ).obj N) ⋙ comap φ) :=
      preservesFiniteColimits_of_natIso (tensorRightExtendScalarsCompComapIso φ N).symm
    have : PreservesFiniteLimits (tensorRight ((extendScalars φ).obj N)) :=
      preservesFiniteLimits_of_reflects_of_preserves _ (comap φ)
    have : PreservesFiniteColimits (tensorRight ((extendScalars φ).obj N)) :=
      preservesFiniteColimits_of_reflects_of_preserves _ (comap φ)
    refine ⟨(exactFunctor_iff _).2
      ⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _).symm,
        preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _).symm⟩,
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩

end CategoryTheory.Mod
