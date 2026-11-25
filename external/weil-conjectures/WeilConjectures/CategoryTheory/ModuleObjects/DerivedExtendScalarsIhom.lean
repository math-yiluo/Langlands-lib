/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsIhomOfProjection
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsIhomProjection
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The derived extension of scalars along a quotient by a nonzerodivisor commutes with internal homs

Let `φ : R ⟶ S` be a morphism of commutative algebra objects of a closed symmetric monoidal
Grothendieck abelian category `C` with functorial flat resolutions, and `k` an integer such that
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact (for instance `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`). This file shows
that the derived extension of scalars `S ⊗ᴸ_R - : D(Mod_R(C)) ⥤ D(Mod_S(C))`, monoidal through
`Functor.leftDerivedFunctorMonoidal`, commutes with internal homs: the comparison
`S ⊗ᴸ_R RHom(A, B) ⟶ RHom(S ⊗ᴸ_R A, S ⊗ᴸ_R B)` is an isomorphism for all `A`, `B`
(`Mod.isIso_ihomComparison_leftDerivedExtendScalars`; blueprint
`proposition-six-operations-change-coefficients--7`).

Write `L = S ⊗ᴸ_R -` and `H = D(Res)` for its right adjoint, which reflects isomorphisms. By the
projection formula (`Mod.isIso_derivedExtendMapDerivedCategoryAdjunction_projectionMorphism`), the
left projection morphisms `K ⊗ᴸ H 𝟙 ⟶ H (L K ⊗ᴸ 𝟙)` are isomorphisms, i.e. `H L K ≅ K ⊗ᴸ S`.
The object `H 𝟙 = S[0]` of `D(Mod_R(C))` is dualizable, `S` having the finite resolution
`R --k--> R` by dualizable objects (`Mod.isDualizable_mapDerivedCategory_tensorUnit`). The result
is then the formal criterion
`Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v + 1} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v + 1} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The unit `𝟙 ≅ S` of `D(Mod_S(C))`, regarded as an `R`-module complex, is the module `S`
placed in degree zero. -/
noncomputable def mapDerivedCategoryTensorUnitIso :
    (DerivedCategory.singleFunctor (Mod C R) 0).obj ((comap φ).obj (𝟙_ (Mod C S))) ≅
      (comap φ).mapDerivedCategory.obj (𝟙_ (DerivedCategory (Mod C S))) :=
  have := DerivedCategory.isIso_ε_Qh (Mod C S)
  (((comap φ : Mod C S ⥤ Mod C R).mapDerivedCategorySingleFunctor 0).app (𝟙_ (Mod C S))).symm ≪≫
    (comap φ).mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso (Mod C S)).symm.app _ ≪≫
        (asIso (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Mod C S)))).symm)

/-- If `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, then `S`, regarded as an object of
`D(Mod_R(C))`, is dualizable. -/
lemma isDualizable_mapDerivedCategory_tensorUnit (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) :
    IsDualizable ((comap φ).mapDerivedCategory.obj (𝟙_ (DerivedCategory (Mod C S)))) := by
  have w' : (k • 𝟙 (𝟙_ (Mod C R))) ≫ regularToComapRegular φ = 0 := hom_ext _ _ w
  have hS : (ShortComplex.mk _ _ w').ShortExact :=
    shortExact_of_shortExact_map_forget (ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)) hφ)
  exact IsDualizable.of_iso (mapDerivedCategoryTensorUnitIso φ)
    (DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hS isDualizable_unit
      isDualizable_unit)


section Braided

attribute [local instance] DerivedCategory.braidedCategory'

/-- **The projection formula for the derived extension of scalars**, left version: the left
projection morphism `K ⊗ᴸ D(Res) N ⟶ D(Res) ((S ⊗ᴸ_R K) ⊗ᴸ N)` is an isomorphism. -/
theorem isIso_derivedExtendMapDerivedCategoryAdjunction_leftProjectionMorphism
    (K : DerivedCategory (Mod C R)) (N : DerivedCategory (Mod C S)) :
    letI := extendScalarsMonoidal φ
    letI := (extendScalars φ).leftDerivedFunctorMonoidal
    IsIso ((derivedExtendMapDerivedCategoryAdjunction φ).leftProjectionMorphism K N) := by
  let := extendScalarsMonoidal φ
  let := (extendScalars φ).leftDerivedFunctorMonoidal
  have := isIso_derivedExtendMapDerivedCategoryAdjunction_projectionMorphism φ N K
  exact Adjunction.isIso_leftProjectionMorphism _ (fun X Y ↦
    ((extendScalars φ).leftDerivedFunctor_map_braiding_hom_δ
      (extendScalars_map_braiding_hom_δ φ) X Y).symm) K N

/-- **The derived extension of scalars along a quotient by a nonzerodivisor commutes with internal
homs**: if `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, the comparison
`S ⊗ᴸ_R RHom(A, B) ⟶ RHom(S ⊗ᴸ_R A, S ⊗ᴸ_R B)` is an isomorphism. -/
theorem isIso_ihomComparison_leftDerivedExtendScalars (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (A B : DerivedCategory (Mod C R)) :
    letI := extendScalarsMonoidal φ
    letI := (extendScalars φ).leftDerivedFunctorMonoidal
    IsIso ((Functor.LaxMonoidal.ihomComparison (extendScalars φ).leftDerivedFunctor A).app
      B) := by
  let := extendScalarsMonoidal φ
  let := (extendScalars φ).leftDerivedFunctorMonoidal
  obtain ⟨hP⟩ := isDualizable_mapDerivedCategory_tensorUnit φ k w hφ
  let := BraidedCategory.exactPairing_swap
    ((comap φ).mapDerivedCategory.obj (𝟙_ (DerivedCategory (Mod C S))))
    ((comap φ).mapDerivedCategory.obj (𝟙_ (DerivedCategory (Mod C S))))ᘁ
  exact Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism _
    (derivedExtendMapDerivedCategoryAdjunction φ)
    ((comap φ).mapDerivedCategory.obj (𝟙_ (DerivedCategory (Mod C S))))ᘁ
    (fun K ↦ isIso_derivedExtendMapDerivedCategoryAdjunction_leftProjectionMorphism φ K _) A B

end Braided
end CategoryTheory.Mod
