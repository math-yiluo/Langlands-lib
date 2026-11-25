/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Finite-filtration devissage through a triangulated derived functor

Source: Stacks Project, Tags 0GKY, 06UQ, and 0152 (blueprint:
lem-weil-pbc-etale-lisse-filtration-devissage).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Finite-filtration dévissage for cohomology under a triangulated functor.

Source: Stacks Project, Tag 0GKY, label `lemma-loc-constant-shriek-rel-dim-1`,
proof final paragraph, using Tags 06UQ and 0152.
(blueprint: lem-weil-pbc-etale-lisse-filtration-devissage).

The proof proceeds by applying the weak-Serre cohomology triangulated-subcategory
lemma, taking the zero step as the base case, obtaining distinguished triangles
from the short exact sequences of successive filtration steps, and inducting on
`i` using closure under the middle vertex.  The argument permits `r = 0`, equal
successive subobjects, and zero quotients.
-/
theorem cohomology_mem_of_filtration
    {A : Type u} {B : Type u'} [Category.{v, u} A] [Category.{v', u'} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    (S : ObjectProperty B) [S.ContainsZero] [S.IsClosedUnderIsomorphisms]
    [S.IsClosedUnderKernels] [S.IsClosedUnderCokernels] [S.IsClosedUnderExtensions]
    (X : A) (r : ℕ) (F : Fin (r + 1) → Subobject X)
    (h₀ : F 0 = ⊥) (hᵣ : F (Fin.last r) = ⊤)
    (hF : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hQ : ∀ (i : Fin r) (q : ℤ),
      S ((DerivedCategory.Plus.homologyFunctor B q).obj
        (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj
          (cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hF i))))))) :
    ∀ q : ℤ, S ((DerivedCategory.Plus.homologyFunctor B q).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) := by
  let := (cohomology_in_weak_serre_subcategory S).1
  let W := (DerivedCategory.homologyProperty S).inverseImage
    (Φ ⋙ DerivedCategory.Plus.ι)
  have h : ∀ i : Fin (r + 1),
      W ((DerivedCategory.Plus.singleFunctor A 0).obj (F i : A)) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      apply W.prop_of_isZero
      apply (DerivedCategory.Plus.singleFunctor A 0).map_isZero
      rw [h₀]
      exact (isZero_zero A).of_iso Subobject.botCoeIsoZero
    | succ i ih =>
      let f := Subobject.ofLE (F i.castSucc) (F i.succ) (hF i)
      have hE : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
        { exact := ShortComplex.exact_cokernel f }
      exact W.ext_of_isTriangulatedClosed₂ _ hE.singleTrianglePlus_distinguished ih (hQ i)
  have hlast := h (Fin.last r)
  rw [hᵣ] at hlast
  exact W.prop_of_iso
    ((DerivedCategory.Plus.singleFunctor A 0).mapIso
      (asIso (⊤ : Subobject X).arrow)) hlast

end CategoryTheory
