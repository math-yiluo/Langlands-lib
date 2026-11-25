/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre

/-! Geometric and shift components of the bounded-constructibility argument. -/

@[expose] public section

universe u u'

open CategoryTheory MonoidalCategory MonoidalClosed
open MonObj Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- A constructible module placed in degree zero stays bounded constructible after any shift.

Source: the shifted-single isomorphism and the defining homology criterion for
`boundedConstructible`. Its cohomology in degree `-n` is the original module, and all
other cohomology objects are zero. Transport constructibility through these isomorphisms.
(blueprint: lem-poincare-constructible-shift-single) -/
theorem boundedConstructible_shift_single
    (M : Mod (Sheaf (Scheme.ProEt.topology X) A) R)
    (hM : IsConstructibleModuleObject R M) (n : ℤ) :
    boundedConstructible R
      ((shiftFunctor _ n).obj ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  let K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R) :=
    (shiftFunctor _ n).obj ((DerivedCategory.singleFunctor _ 0).obj M)
  let e : K ≅ (DerivedCategory.singleFunctor _ (-n)).obj M :=
    ((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by simp)).app M
  have : K.IsGE (-n) := DerivedCategory.TStructure.t.isGE_of_iso e.symm (-n)
  have : K.IsLE (-n) := DerivedCategory.TStructure.t.isLE_of_iso e.symm (-n)
  apply (mem_boundedConstructible_iff R K).mpr
  constructor
  · refine ⟨-n, -n, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE K (-n) i hi
    · exact DerivedCategory.isZero_of_isLE K (-n) i hi
  · intro i
    by_cases hi : i = -n
    · subst i
      obtain ⟨S, hS⟩ := hM
      exact ⟨S, fun a ↦ lfp_of_iso (hS a)
        (((ProEtale.upperStar A (S.immersion a)).mapMod R).mapIso
          (((DerivedCategory.homologyFunctor _ (-n)).mapIso e) ≪≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-n)).app M).symm)⟩
    · apply constructible_of_isZero R
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE K (-n) i hi
      · exact DerivedCategory.isZero_of_isLE K (-n) i hi

end AlgebraicGeometry.ProEtale
