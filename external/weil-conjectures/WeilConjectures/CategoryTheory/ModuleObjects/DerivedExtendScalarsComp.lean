/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-!

# Transitivity of the derived extension of scalars of module objects

Let `C` be a closed symmetric monoidal Grothendieck abelian category with functorial flat
resolutions and `φ : R ⟶ S`, `ψ : S ⟶ T`, `χ : R ⟶ T` morphisms of commutative algebra objects
with `φ ≫ ψ = χ`. The derived extensions of scalars satisfy
```
T ⊗ᴸ_R - ≅ (T ⊗ᴸ_S -) ∘ (S ⊗ᴸ_R -)
```
(`Mod.derivedExtendScalarsCompIso`), with no flatness hypothesis: both sides are left adjoint
to the levelwise restriction of scalars along `χ = φ ≫ ψ`, and the isomorphism is the conjugate
of the composition isomorphism of the restrictions of scalars.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  [IsCommMonObj T] (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]

/-- The levelwise restrictions of scalars compose: `D(comap ψ) ⋙ D(comap φ) ≅ D(comap χ)` for
`φ ≫ ψ = χ`. -/
noncomputable def mapDerivedCategoryComapCompIso (h : φ ≫ ψ = χ) :
    (comap ψ : Mod C T ⥤ Mod C S).mapDerivedCategory ⋙
        (comap φ : Mod C S ⥤ Mod C R).mapDerivedCategory ≅
      (comap χ : Mod C T ⥤ Mod C R).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (comap ψ) (comap φ) ≪≫
    Functor.mapDerivedCategoryNatIso ((comapComp φ ψ).symm ≪≫ comapCongr h)

/-- **Transitivity of the derived extension of scalars**: for `φ ≫ ψ = χ`,
`T ⊗ᴸ_R - ≅ (T ⊗ᴸ_S -) ∘ (S ⊗ᴸ_R -)`. Both functors are left adjoint to `D(comap χ)`, and the
isomorphism is the conjugate of `Mod.mapDerivedCategoryComapCompIso`. -/
noncomputable def derivedExtendScalarsCompIso (h : φ ≫ ψ = χ) :
    (extendScalars χ).leftDerivedFunctor ≅
      (extendScalars φ).leftDerivedFunctor ⋙ (extendScalars ψ).leftDerivedFunctor :=
  (conjugateIsoEquiv ((derivedExtendMapDerivedCategoryAdjunction φ).comp
      (derivedExtendMapDerivedCategoryAdjunction ψ))
    (derivedExtendMapDerivedCategoryAdjunction χ)).symm
    (mapDerivedCategoryComapCompIso φ ψ χ h)

end CategoryTheory.Mod
