/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Exact conservative functors induce conservative functors on derived categories

If an exact functor `F : A ⥤ B` of abelian categories reflects isomorphisms, so does the
induced functor `D(F) : D(A) ⥤ D(B)`: a morphism of `D(A)` is an isomorphism as soon as it
induces isomorphisms on all cohomology objects, and `D(F)` commutes with cohomology
(`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- An exact functor reflecting isomorphisms induces a functor on derived categories reflecting
isomorphisms: a morphism is an isomorphism iff it is one on all homology objects, and
`F.mapDerivedCategory` commutes with homology. -/
instance reflectsIsomorphisms_mapDerivedCategory (F : A ⥤ B) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso (F.map ((DerivedCategory.homologyFunctor A n).map f)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ F

end CategoryTheory.Functor
