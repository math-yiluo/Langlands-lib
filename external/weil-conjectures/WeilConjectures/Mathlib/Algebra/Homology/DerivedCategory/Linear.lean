/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Localization.Linear

/-!
# Linearity of the homology functors, and torsion in the derived category

The homology functors of complexes and of the derived category of an `R`-linear abelian
category are `R`-linear. If an integer `N` kills every object of an abelian category `C`, then
it kills every object of the derived category `D(C)`.
-/

@[expose] public section

open CategoryTheory

universe w v u' u

namespace HomologicalComplex

variable {C : Type u'} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
  (R : Type w) [Ring R] [Linear R C] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- The homology functor of homological complexes in an `R`-linear category is `R`-linear. -/
instance linear_homologyFunctor : (homologyFunctor C c i).Linear R where
  map_smul φ r := ShortComplex.homologyMap_smul ((shortComplexFunctor C c i).map φ) r

end HomologicalComplex

namespace DerivedCategory

section

variable {C : Type u'} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (R : Type*) [Ring R] [Linear R C]

/-- The homology functors of the derived category of an `R`-linear abelian category are
`R`-linear: they are induced by the `R`-linear homology functors of complexes. -/
instance linear_homologyFunctor (n : ℤ) : (homologyFunctor C n).Linear R := by
  have : Localization.Lifting Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) (homologyFunctor C n) :=
    ⟨homologyFunctorFactors C n⟩
  rw [← Localization.functor_linear_iff Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) R
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) (homologyFunctor C n)]
  infer_instance

end

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `N • 𝟙 M = 0` for every object `M` of `C`, then `N • 𝟙 K = 0` for every object `K` of
the derived category `D(C)`: `K` is the image under `Q` of a complex, which is killed by `N`
degreewise. -/
lemma nsmul_id_eq_zero_of_forall {N : ℕ} (h : ∀ M : C, N • 𝟙 M = 0) (K : DerivedCategory C) :
    N • 𝟙 K = 0 := by
  let e := Q.objObjPreimageIso K
  have hL : N • 𝟙 (Q.objPreimage K) = 0 := by
    ext n
    simp [h]
  have hQ : N • 𝟙 (Q.obj (Q.objPreimage K)) = 0 := by
    rw [← Q.map_id, ← Functor.map_nsmul, hL, Q.map_zero]
  rw [← cancel_epi e.hom, Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp e.hom,
    ← Preadditive.nsmul_comp, hQ, Limits.zero_comp, Limits.comp_zero]

end DerivedCategory
