/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-!

# The derived extension of scalars

Let `C` be a closed symmetric monoidal Grothendieck abelian category with functorial flat
resolutions, as in `WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`, and let
`φ : R ⟶ S` be a morphism of commutative algebra objects of `C`. Extension of scalars
`S ⊗_R - : Mod C R ⥤ Mod C S` is right exact but not exact, and its *derived* version is the
total left derived functor
```
S ⊗ᴸ_R - = L(extendScalars φ) : D(Mod_R(C)) ⥤ D(Mod_S(C)),
```
computed by applying `S ⊗_R -` to a K-flat resolution. It is the generic
`Functor.leftDerivedFunctor` of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`
applied to `Mod.extendScalars φ`; the only functor-specific input is that extension of scalars
preserves quasi-isomorphisms between K-flat complexes (`Mod.preservesKFlatQuasiIso`).

Restriction of scalars `Mod.comap φ : Mod C S ⥤ Mod C R` is exact (kernels and cokernels of
module objects are computed in `C` on both sides, `Mod.preservesFiniteLimits_comap` and
`Mod.preservesFiniteColimits_comap`), so its right derived functor is the levelwise functor
`(comap φ).mapDerivedCategory` (`Mod.rightDerivedComapIsoMapDerivedCategory`). The adjunction
between extension and restriction of scalars derives to the adjunction
```
S ⊗ᴸ_R - ⊣ D(comap φ)
```
(`Mod.derivedExtendRestrictAdjunction`, `Mod.derivedExtendMapDerivedCategoryAdjunction`).

## Sorried input

* `Mod.preservesKFlatQuasiIso`: if `f : K ⟶ L` is a quasi-isomorphism between K-flat complexes
  of `R`-modules, then `S ⊗_R f` is a quasi-isomorphism. Indeed, the cone `P` of `f` is acyclic
  and K-flat, and `S ⊗_R P` is acyclic: choosing a K-flat resolution `Q ⟶ S` of `S` as an
  `R`-module, `Q ⊗_R P ⟶ S ⊗_R P` is a quasi-isomorphism since `P` is K-flat, and `Q ⊗_R P` is
  acyclic since `Q` is K-flat and `P` is acyclic. Finally the underlying complex of `S ⊗_R P`
  in `Mod C R` is `S ⊗_R P` with `S` regarded as an `R`-module through `φ`, and restriction of
  scalars is exact, hence detects acyclicity.

The remaining `sorry`s of this file are inherited from
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

/-! ### Exactness of restriction of scalars -/

section Exact

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

/-- Restriction of scalars is left exact: limits of module objects are computed in `C` on
both sides. -/
instance preservesFiniteLimits_comap : PreservesFiniteLimits (comap φ : Mod C S ⥤ Mod C R) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J ((comap φ : Mod C S ⥤ Mod C R) ⋙ forget R) :=
      inferInstanceAs (PreservesLimitsOfShape J (forget S : Mod C S ⥤ C))
    have : ReflectsLimitsOfShape J (forget R : Mod C R ⥤ C) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    preservesLimitsOfShape_of_reflects_of_preserves (comap φ) (forget R)

/-- Restriction of scalars is right exact: colimits of module objects are computed in `C` on
both sides. -/
instance preservesFiniteColimits_comap :
    PreservesFiniteColimits (comap φ : Mod C S ⥤ Mod C R) where
  preservesFiniteColimits J _ _ :=
    have : PreservesColimitsOfShape J ((comap φ : Mod C S ⥤ Mod C R) ⋙ forget R) :=
      inferInstanceAs (PreservesColimitsOfShape J (forget S : Mod C S ⥤ C))
    have : ReflectsColimitsOfShape J (forget R : Mod C R ⥤ C) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    preservesColimitsOfShape_of_reflects_of_preserves (comap φ) (forget R)

end Exact

/-! ### The derived extension of scalars -/

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- `ℤ`-indexed colimits of module objects are exact: `Mod C R` is Grothendieck abelian. -/
instance hasExactColimitsOfShape_int : HasExactColimitsOfShape ℤ (Mod C R) :=
  have := AB5OfSize_of_univLE.{0, 0} (Mod C R)
  inferInstance

omit [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  [IsCommMonObj R] in
/-- The right action on the restricted regular module is multiplication after scalar change. -/
lemma restrictedRegular_rightAction :
    (β_ S R).hom ≫ γ[R,((comap φ).obj (regular S)).X] = S ◁ φ ≫ μ[S] := by
  change (β_ S R).hom ≫ φ ▷ S ≫ μ[S] = _
  rw [← BraidedCategory.braiding_naturality_right_assoc, IsCommMonObj.mul_comm]

/-- The underlying object of `S ⊗_R M` (extension of scalars along `φ`) is the underlying object
of the tensor product of `M` with `S` regarded as an `R`-module. -/
noncomputable def extendForgetTensorObjIso (M : Mod C R) :
    (extendScalarsObj φ M).X ≅ (((comap φ).obj (regular S)) ⊗ M).X where
  hom := extendDescHom φ (tensorObjπ ((comap φ).obj (regular S)) M) (by
    rw [← restrictedRegular_rightAction φ]
    exact tensorObjπ_condition ((comap φ).obj (regular S)) M)
  inv := coequalizer.desc (extendπ φ M) (by
    change ((β_ S R).hom ≫ γ[R,((comap φ).obj (regular S)).X]) ▷ M.X ≫
        extendπ φ M = _
    rw [restrictedRegular_rightAction φ]
    exact extendπ_condition φ M)
  hom_inv_id := by
    apply coequalizer.hom_ext
    simp only [extendDescHom, extendπ, tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl
  inv_hom_id := by
    apply coequalizer.hom_ext
    simp only [extendDescHom, extendπ, tensorObjπ, coequalizer.π_desc_assoc]
    erw [coequalizer.π_desc, Category.comp_id]
    rfl

/-- Extension of scalars followed by the forgetful functor is tensoring with `S` regarded as an
`R`-module followed by the forgetful functor: the square

```
Mod_R ──extendScalars φ──▶ Mod_S
  │ φ^*S ⊗ -                 │ forget
  ▼                          ▼
Mod_R ───────forget──────▶   C
```

commutes up to this natural isomorphism. -/
noncomputable def extendForgetTensorIso :
    extendScalars φ ⋙ forget S ≅
      tensorLeft ((comap φ).obj (regular S)) ⋙ forget R :=
  NatIso.ofComponents (extendForgetTensorObjIso φ) (by
    intro M N f
    apply (cancel_epi (extendπ φ M)).1
    simp [extendForgetTensorObjIso, extendπ_extendScalarsMap_assoc,
      tensorObjπ_whiskerLeft]
    rfl)

/-- Extension of scalars sends quasi-isomorphisms between K-flat complexes of `R`-modules to
quasi-isomorphisms; see the module docstring for the argument. -/
instance preservesKFlatQuasiIso : (extendScalars φ).PreservesKFlatQuasiIso := by
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa
    ((comap φ).obj (regular S))
  have hl := ht.of_iso
    ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight ((comap φ).obj (regular S))) _).app K).symm
  have hf := hl.map (forget R)
  have he : (((extendScalars φ ⋙ forget S).mapHomologicalComplex _).obj K).Acyclic :=
    hf.of_iso ((NatIso.mapHomologicalComplex (extendForgetTensorIso φ) _).app K).symm
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ (forget S)).1 (he n)

open scoped CategoryTheory.Functor in
/-- The derived extension of scalars `S ⊗ᴸ_R - : D(Mod_R(C)) ⥤ D(Mod_S(C))`, the total left
derived functor of `S ⊗_R -`, computed on K-flat resolutions.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`, written
`L(-)`, applied to `Mod.extendScalars φ`. -/
noncomputable example : DerivedCategory (Mod C R) ⥤ DerivedCategory (Mod C S) :=
  L(extendScalars φ)

/-- The derived adjunction `S ⊗ᴸ_R - ⊣ R(comap φ)` between the derived extension of scalars
and the right derived functor of restriction of scalars. -/
noncomputable def derivedExtendRestrictAdjunction :
    (extendScalars φ).leftDerivedFunctor ⊣ (comap φ).rightDerivedFunctor :=
  (extendRestrictAdjunction φ).derivedAdjunction

/-- Since restriction of scalars is exact, its right derived functor is the levelwise
functor `D(comap φ)`. -/
noncomputable def rightDerivedComapIsoMapDerivedCategory :
    (comap φ : Mod C S ⥤ Mod C R).rightDerivedFunctor ≅ (comap φ).mapDerivedCategory :=
  (comap φ).rightDerivedFunctorIsoMapDerivedCategory

/-- The derived adjunction `S ⊗ᴸ_R - ⊣ D(comap φ)` between the derived extension of scalars
and the levelwise restriction of scalars on the derived categories. -/
noncomputable def derivedExtendMapDerivedCategoryAdjunction :
    (extendScalars φ).leftDerivedFunctor ⊣ (comap φ).mapDerivedCategory :=
  (derivedExtendRestrictAdjunction φ).ofNatIsoRight (rightDerivedComapIsoMapDerivedCategory φ)

end CategoryTheory.Mod
