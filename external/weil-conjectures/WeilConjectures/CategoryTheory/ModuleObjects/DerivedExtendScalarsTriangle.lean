/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!

# The reduction triangle of the derived extension of scalars along `R ⟶ R ⧸ k`

Let `C` be a closed symmetric monoidal Grothendieck abelian category with functorial flat
resolutions and `φ : R ⟶ S` a morphism of commutative algebra objects such that
`0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, for an integer `k`: `S = R ⧸ k` and `k` is a
nonzerodivisor on `R`. Then `S` has the flat resolution `R --k--> R`, and for every
`K ∈ D(Mod_R(C))` there is a distinguished triangle
```
K --k--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]
```
in `D(Mod_R(C))`, where `S ⊗ᴸ_R K` is regarded as a complex of `R`-modules
(`Mod.exists_distinguished_zsmul_derivedExtendScalars`).

Indeed `K` is represented by a K-flat complex `P` of flat `R`-modules
(`CochainComplex.exists_quasiIso_flat_kFlat`), on which the derived extension of scalars is
computed by `S ⊗_R P`, and `0 ⟶ P --k--> P ⟶ S ⊗_R P ⟶ 0` is a short exact sequence of complexes
(`Mod.shortExact_extendUnit`).

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits Pretriangulated

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

omit [Abelian.HasFunctorialFlatResolution C] in
/-- The unit `P ⟶ S ⊗_R P` on a complex of `R`-modules, as a morphism of complexes. -/
@[simps]
noncomputable def extendUnitComplexHom (P : CochainComplex (Mod C R) ℤ) :
    P ⟶ ((extendScalars φ ⋙ comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P where
  f i := extendUnit φ (P.X i)
  comm' i j _ := by
    rw [← extendRestrictAdjunction_unit_app, ← extendRestrictAdjunction_unit_app]
    exact ((extendRestrictAdjunction φ).unit.naturality (P.d i j)).symm

variable {φ}

omit [Abelian.HasFunctorialFlatResolution C] in
/-- For a complex `P` of flat `R`-modules, `0 ⟶ P --k--> P ⟶ S ⊗_R P ⟶ 0` is a short exact
sequence of complexes. -/
lemma shortExact_extendUnitComplexHom (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (P : CochainComplex (Mod C R) ℤ)
    (hP : ∀ n, ObjectProperty.flat (P.X n)) :
    (ShortComplex.mk (k • 𝟙 P) (extendUnitComplexHom φ P) (by
      ext i
      simpa using congrArg Hom.hom (zsmul_comp_extendUnit k w (P.X i)))).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp))
    (shortExact_extendUnit k w hφ (P.X i) (hP i))

/-- **The reduction triangle**: if `0 ⟶ R --k--> R --φ--> S ⟶ 0` is short exact, then for every
`K ∈ D(Mod_R(C))` there is a distinguished triangle `K --k--> K ⟶ S ⊗ᴸ_R K ⟶ K[1]`, where the
derived extension of scalars `S ⊗ᴸ_R K` is regarded as a complex of `R`-modules. -/
theorem exists_distinguished_zsmul_derivedExtendScalars (k : ℤ) (w : (k • 𝟙 R) ≫ φ = 0)
    (hφ : (ShortComplex.mk _ _ w).ShortExact) (K : DerivedCategory (Mod C R)) :
    ∃ (g : K ⟶ (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K))
      (h : (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) ⟶
        K⟦(1 : ℤ)⟧),
      Triangle.mk (k • 𝟙 K) g h ∈ distTriang (DerivedCategory (Mod C R)) := by
  obtain ⟨P, π, _, hflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have hS := shortExact_extendUnitComplexHom k w hφ P hflat
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  let e₁ : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let e₃ : DerivedCategory.Q.obj
      (((extendScalars φ ⋙ comap φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj K) :=
    ((comap φ).mapDerivedCategoryFactors.app
        (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C S)).app
            (((extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso
        (asIso ((extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P))).symm ≪≫
      (comap φ).mapDerivedCategory.mapIso ((extendScalars φ).leftDerivedFunctor.mapIso
        ((DerivedCategory.quotientCompQhIso (Mod C R)).app P ≪≫ e₁))
  refine ⟨e₁.inv ≫ DerivedCategory.Q.map (extendUnitComplexHom φ P) ≫ e₃.hom,
    e₃.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₁.hom⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ e₁ e₁ e₃ ?_ ?_ ?_).symm
  · simp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₁, Functor.map_zsmul,
      Functor.map_id, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    erw [Category.id_comp, Category.comp_id]
  · simp [DerivedCategory.triangleOfSES]
  · simp [DerivedCategory.triangleOfSES]

end CategoryTheory.Mod
