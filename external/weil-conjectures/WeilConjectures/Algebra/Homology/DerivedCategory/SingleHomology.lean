/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The homology of an object of the derived category concentrated in one degree

If `M` in the derived category `D(C)` of an abelian category is isomorphic to an object `A`
placed in degree `n`, then the homology of `M` vanishes outside degree `n` and `Hⁿ(M) ≅ A`.

## Main statements

- `DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor`: `Hⁱ(M) = 0` for `i ≠ n`.
- `DerivedCategory.homologyFunctorObjIsoOfIsoSingleFunctor`: `Hⁿ(M) ≅ A`.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {M : DerivedCategory C} {A : C} {n : ℤ}

/-- If `M ≅ A[-n]` is concentrated in degree `n`, then `Hⁱ(M) = 0` for `i ≠ n`.

(blueprint: `lem-pc-degree-zero-properties`) -/
lemma isZero_homologyFunctor_obj_of_iso_singleFunctor (e : M ≅ (singleFunctor C n).obj A)
    {i : ℤ} (hi : i ≠ n) : IsZero ((homologyFunctor C i).obj M) := by
  refine IsZero.of_iso ?_ ((homologyFunctor C i).mapIso e)
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact isZero_of_isGE _ n i hi
  · exact isZero_of_isLE _ n i hi

/-- If `M ≅ A[-n]` is concentrated in degree `n`, then `Hⁿ(M) ≅ A`.

(blueprint: `lem-pc-degree-zero-properties`) -/
noncomputable def homologyFunctorObjIsoOfIsoSingleFunctor (e : M ≅ (singleFunctor C n).obj A) :
    (homologyFunctor C n).obj M ≅ A :=
  (homologyFunctor C n).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C n).app A

end DerivedCategory
