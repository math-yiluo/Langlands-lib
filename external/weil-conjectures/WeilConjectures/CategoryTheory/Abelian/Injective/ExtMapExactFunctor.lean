/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExtExactFunctorCocycle
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.CategoryTheory.Preadditive.Injective.ResolutionMap

/-!
# Exact functors on `Ext` classes of cocycles

For an exact functor `F` preserving injective objects and an injective resolution `R` of `Y`, the
image under `F` of the class `R.extMk f` of a cocycle `f : X ⟶ Rⁿ` is the class of the cocycle
`F f : F X ⟶ F Rⁿ` for the injective resolution `F(R)` of `F Y`
(`CategoryTheory.InjectiveResolution.mk₀_comp_mapExactFunctor_extMk`).
-/

@[expose] public section

universe v w w'

open CategoryTheory CochainComplex HomComplex Limits Abelian

namespace CategoryTheory.InjectiveResolution

variable {C : Type w} {D : Type w'} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  [HasExt.{v} C] [HasExt.{v} D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesInjectiveObjects]

/-- The image under an exact functor of the class of a cocycle `f : X ⟶ Rⁿ`, precomposed with
`α : X' ⟶ F X`, is the class of the cocycle `α ≫ F f` for the resolution `F(R)`. -/
theorem mk₀_comp_mapExactFunctor_extMk {X Y : C} {X' : D} (α : X' ⟶ F.obj X)
    (R : InjectiveResolution Y) {n : ℕ} (f : X ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    (Ext.mk₀ α).comp ((R.extMk f (n + 1) rfl hf).mapExactFunctor F) (zero_add n) =
      (R.map F).extMk (α ≫ F.map f) (n + 1) rfl
        (by rw [map_cocomplex_d, Category.assoc, ← F.map_comp, hf, F.map_zero, comp_zero]) := by
  have hφ : (F.mapHomologicalComplex (.up ℤ)).map R.ι' ≫
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app Y ≫ (R.map F).ι' := by
    ext i
    by_cases hi : i = 0
    swap
    · exact (F.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)).eq_of_src _ _
    subst hi
    have h0 : ComplexShape.embeddingUpNat.r (0 : ℤ) = some 0 := by
      simpa using ComplexShape.embeddingUpNat.r_f 0
    simp [ι'_f_zero, HomologicalComplex.mapExtendIso, cochainComplexXIso,
      HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToHom_map,
      HomologicalComplex.mapExtendX_hom_eq R.cocomplex F h0]
  have ha : (f ≫ (R.cochainComplexXIso n n rfl).inv) ≫ R.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) =
      0 := by
    rw [R.cochainComplex_d _ _ n (n + 1) rfl (by push_cast; rfl)]
    simp [reassoc_of% hf]
  have hiso : F.map (f ≫ (R.cochainComplexXIso n n rfl).inv) ≫
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom.f (n : ℤ) =
      F.map f ≫ ((R.map F).cochainComplexXIso n n rfl).inv := by
    simp only [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
    rw [
      HomologicalComplex.mapExtendX_hom_eq _ _ (j := n)
        (by simpa using ComplexShape.embeddingUpNat.r_f n)]
    simp [cochainComplexXIso, HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      eqToHom_map]
  have key := ext_mapExactFunctor_cocycle F α R (R.map F) _ ⟨Homotopy.ofEq hφ⟩ n
    (f ≫ (R.cochainComplexXIso n n rfl).inv) ha
    (by rw [Category.assoc, hiso, ← Category.assoc, ← Category.assoc]
        rw [(R.map F).cochainComplex_d _ _ n (n + 1) rfl (by push_cast; rfl)]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [map_cocomplex_d, ← F.map_comp_assoc, hf, F.map_zero]
        simp)
  refine key.trans ?_
  simp only [extMk]
  congr 3
  rw [hiso, Category.assoc]

end CategoryTheory.InjectiveResolution
