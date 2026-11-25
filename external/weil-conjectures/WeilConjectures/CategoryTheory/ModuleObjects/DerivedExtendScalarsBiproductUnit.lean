/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Center.Linear
public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Biproduct decompositions by the unit of the derived extension of scalars

Let `φ : R ⟶ S` be a flat morphism of commutative algebra objects, so that extension of scalars
`S ⊗_R -` is exact, and suppose that `Mod C S` is `k`-linear. For scalars `b : Fin d → k`,
consider the maps `M ⟶ φ^* (S ⊗_R M)`, `m ↦ bᵢ ⊗ m`: the unit of extension and restriction of
scalars followed by the multiplication by `bᵢ`. If they exhibit `φ^* (S ⊗_R M)` as the direct
sum of `d` copies of `M` for every `R`-module `M`, then the same holds for the derived unit
`K ⟶ D(φ^*) (S ⊗ᴸ_R K)` on the derived category
(`CategoryTheory.Mod.isIso_biproductDesc_derivedUnit_smul`): on a complex `M`, the derived map is
the image of the levelwise map, which is a levelwise isomorphism.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]
  {k : Type*} [CommRing k] [Linear k (Mod C S)] {d : ℕ} (b : Fin d → k)

/-- The levelwise version of `Mod.isIso_biproductDesc_derivedUnit_smul`: if the maps
`M ⟶ φ^* (S ⊗_R M)`, `m ↦ bᵢ ⊗ m`, exhibit `φ^* (S ⊗_R M)` as `Mᵈ` for every `R`-module `M`, then
so do the corresponding maps of complexes. -/
lemma isIso_biproductDesc_unit_smul_complex
    [HasFiniteBiproducts (CochainComplex (Mod C R) ℤ)]
    (hb : ∀ M : Mod C R, IsIso (biproduct.desc fun i : Fin d ↦
      (extendRestrictAdjunction φ).unit.app M ≫ (comap φ).map (b i • 𝟙 _)))
    (M : CochainComplex (Mod C R) ℤ) :
    IsIso (biproduct.desc fun i : Fin d ↦
      ((extendRestrictAdjunction φ).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M ≫
        ((comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).map (b i • 𝟙 _)) := by
  have (n : ℤ) : IsIso ((biproduct.desc fun i : Fin d ↦
      ((extendRestrictAdjunction φ).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M ≫
        ((comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).map (b i • 𝟙 _)).f n) := by
    refine ((HomologicalComplex.eval _ _ n).isIso_map_biproductDesc _).2 ?_
    simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f,
      Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    exact hb (M.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

variable [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj S]
  [PreservesFiniteLimits (extendScalars φ)]

/-- **The derived unit followed by scalar multiplications is a biproduct decomposition.** Let
`φ : R ⟶ S` be a morphism of commutative algebra objects with exact extension of scalars, and
`b : Fin d → k` scalars acting on `S`-modules. If the maps `M ⟶ φ^* (S ⊗_R M)`, `m ↦ bᵢ ⊗ m`
(the unit followed by the multiplication by `bᵢ`) exhibit `φ^* (S ⊗_R M)` as `Mᵈ` for every
`R`-module `M`, then the maps `K ⟶ D(φ^*) (S ⊗ᴸ_R K)` given by the unit of the derived adjunction
followed by the multiplication by `bᵢ` exhibit `D(φ^*) (S ⊗ᴸ_R K)` as `Kᵈ`, for every `K` in the
derived category. -/
theorem isIso_biproductDesc_derivedUnit_smul
    (hb : ∀ M : Mod C R, IsIso (biproduct.desc fun i : Fin d ↦
      (extendRestrictAdjunction φ).unit.app M ≫ (comap φ).map (b i • 𝟙 _)))
    (K : DerivedCategory (Mod C R)) :
    IsIso (biproduct.desc fun i : Fin d ↦
      (derivedExtendMapDerivedCategoryAdjunction φ).unit.app K ≫
        (comap φ).mapDerivedCategory.map
          (b i • 𝟙 ((extendScalars φ).leftDerivedFunctor.obj K))) := by
  let adj := derivedExtendMapDerivedCategoryAdjunction φ
  let sc (i : Fin d) := (Linear.toCatCenter k (DerivedCategory (Mod C S)) (b i)).asHom
  let q := HomotopyCategory.quotient (Mod C R) (ComplexShape.up ℤ)
  suffices h : ∀ M : CochainComplex (Mod C R) ℤ,
      IsIso ((adj.biproductDescUnit sc).app (DerivedCategory.Qh.obj (q.obj M))) by
    exact (NatTrans.isIso_app_iff_of_iso (adj.biproductDescUnit sc)
      ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
        DerivedCategory.Q.objObjPreimageIso K)).1 (h (DerivedCategory.Q.objPreimage K))
  intro M
  have : HasFiniteBiproducts (CochainComplex (Mod C R) ℤ) := .of_hasFiniteProducts
  let c := (comap φ).mapDerivedCategory.map
      ((extendScalars φ).leftDerivedFunctorCounit.app (q.obj M)) ≫
    (comap φ).mapDerivedCategoryFactorsh.hom.app
      (((extendScalars φ).mapHomotopyCategory _).obj (q.obj M))
  have key : (adj.biproductDescUnit sc).app (DerivedCategory.Qh.obj (q.obj M)) ≫ c =
      biproduct.desc fun i ↦ (q ⋙ DerivedCategory.Qh).map
        (((extendRestrictAdjunction φ).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M ≫
          ((comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).map (b i • 𝟙 _)) := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    have hfac := derivedExtendMapDerivedCategoryAdjunction_unit_app_fac φ (q.obj M)
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hfac
    have hnat := (comap φ).mapDerivedCategoryFactorsh.hom.naturality
      ((HomotopyCategory.quotient _ _).map
        (b i • 𝟙 (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))
    have hsmul : b i • 𝟙 (DerivedCategory.Qh.obj
        (((extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj (q.obj M))) =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (b i • 𝟙 (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) := by
      rw [Functor.map_smul, Functor.map_smul, Functor.map_id, Functor.map_id]
      rfl
    have hcomm : (comap φ).mapDerivedCategory.map
          (b i • 𝟙 ((extendScalars φ).leftDerivedFunctor.obj (DerivedCategory.Qh.obj (q.obj M)))) ≫
        (comap φ).mapDerivedCategory.map
          ((extendScalars φ).leftDerivedFunctorCounit.app (q.obj M)) =
        (comap φ).mapDerivedCategory.map
          ((extendScalars φ).leftDerivedFunctorCounit.app (q.obj M)) ≫
        (comap φ).mapDerivedCategory.map (b i • 𝟙 _) := by
      rw [← Functor.map_comp, ← Functor.map_comp, Linear.smul_comp, Linear.comp_smul,
        Category.id_comp, Category.comp_id]
    simp only [Functor.comp_obj, Functor.comp_map] at hnat
    simp only [Adjunction.biproductDescUnit_app, biproduct.ι_desc_assoc, biproduct.ι_desc,
      Category.assoc, c, sc, Linear.toCatCenter_apply_asHom_app, Functor.comp_map, Functor.map_comp]
    rw [reassoc_of% hcomm, hsmul]
    erw [hnat, reassoc_of% hfac]
    rfl
  rw [← isIso_comp_right_iff _ c, key, ← Functor.isIso_map_biproductDesc]
  exact @Functor.map_isIso _ _ _ _ _ _ (q ⋙ DerivedCategory.Qh) _
    (isIso_biproductDesc_unit_smul_complex φ b hb M)

end CategoryTheory.Mod
