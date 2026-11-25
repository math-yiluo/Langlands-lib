/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Zero morphisms and epimorphisms detected by a family which jointly reflects isomorphisms

A family of left exact functors between abelian categories which jointly reflects
isomorphisms detects the morphisms that are zero, and the epimorphisms: this file proves
these two criteria, next to the criteria of
`Mathlib/CategoryTheory/Functor/ReflectsIso/Exact.lean` for exactness and short exactness.

Those criteria, `CategoryTheory.JointlyReflectIsomorphisms.isZero_iff`, `.exact_iff` and
`.shortExact_iff`, ask for the target categories `D i` to be abelian and for the functors
`F i` to be exact. This file also discharges those hypotheses for the two-element family
`CategoryTheory.pairFunctor` of a pair of exact functors between abelian categories, so that
the three criteria apply to a pair of functors out of the box.

## Main results

- `CategoryTheory.JointlyReflectIsomorphisms.eq_zero_of_map_eq_zero`: a morphism sent to
  zero by every member of the family is zero.
- `CategoryTheory.JointlyReflectIsomorphisms.epi_of_epi_map`: a morphism sent to an
  epimorphism by every member of the family is an epimorphism.
- `CategoryTheory.JointlyReflectIsomorphisms.exactFunctor_of_iso`: a functor which becomes
  exact after a jointly conservative family of exact functors is exact.

-/

@[expose] public section

universe v₁ v u₁ u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [Abelian C] {I : Type*} {D : I → Type*}
  [∀ i, Category (D i)] [∀ i, Abelian (D i)] {F : ∀ i, C ⥤ D i}
  [∀ i, PreservesFiniteLimits (F i)]

namespace JointlyReflectIsomorphisms

/-- **A family of left exact functors which jointly reflects isomorphisms detects the zero
morphisms.** Indeed, the kernel inclusion of a morphism `φ` killed by every `F i` becomes
invertible under every `F i`, by the comparison square
```
     (F i).obj (kernel φ) --(F i).map (kernel.ι φ)--> (F i).obj X
              |                                            ‖
    kernelComparison φ (F i)                               ‖
              ↓                                            ‖
     kernel ((F i).map φ) ---------kernel.ι-----------> (F i).obj X
```
whose left vertical map is invertible since `F i` is left exact; so `kernel.ι φ` is
invertible and `φ = 0`. -/
lemma eq_zero_of_map_eq_zero (hP : JointlyReflectIsomorphisms F) {X Y : C} (φ : X ⟶ Y)
    (h : ∀ i, (F i).map φ = 0) : φ = 0 := by
  have : IsIso (kernel.ι φ) := by
    have (i : I) : IsIso ((F i).map (kernel.ι φ)) := by
      rw [← kernelComparison_comp_ι φ (F i)]
      have : IsIso (kernel.ι ((F i).map φ)) := kernel.ι_of_zero (h i)
      infer_instance
    exact hP.isIso (kernel.ι φ)
  rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]

/-- **A family of left exact functors which jointly reflects isomorphisms detects the
epimorphisms.** Indeed, the cokernel projection of a morphism `φ` sent to an epimorphism by
every `F i` is killed by every `F i`, by the comparison square
```
     (F i).obj Y ----(F i).map (cokernel.π φ)---> (F i).obj (cokernel φ)
          ‖                                                ↑
          ‖                                   cokernelComparison φ (F i)
          ‖                                                |
     (F i).obj Y --------cokernel.π-----------> cokernel ((F i).map φ)
```
whose bottom map is zero; so `cokernel.π φ = 0` by
`CategoryTheory.JointlyReflectIsomorphisms.eq_zero_of_map_eq_zero` and `φ` is an
epimorphism. -/
lemma epi_of_epi_map (hP : JointlyReflectIsomorphisms F) {X Y : C} (φ : X ⟶ Y)
    (h : ∀ i, Epi ((F i).map φ)) : Epi φ := by
  refine Abelian.epi_of_cokernel_π_eq_zero φ (hP.eq_zero_of_map_eq_zero _ fun i ↦ ?_)
  have := h i
  rw [← π_comp_cokernelComparison φ (F i), cokernel.π_of_epi, zero_comp]

end JointlyReflectIsomorphisms

end

section

variable {C : Type*} [Category* C] [Abelian C] {C' : Type*} [Category* C'] [Abelian C']
  {I : Type*} {D : I → Type*} [∀ i, Category* (D i)] [∀ i, Abelian (D i)]
  {D' : I → Type*} [∀ i, Category* (D' i)] [∀ i, Abelian (D' i)]
  {F : ∀ i, C ⥤ D i} [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  {F' : ∀ i, C' ⥤ D' i} [∀ i, PreservesFiniteLimits (F' i)] [∀ i, PreservesFiniteColimits (F' i)]

/-- **A functor which is exact after a jointly conservative family of exact functors is
exact.** Let `T : C ⥤ C'` be an additive functor such that for every `i` there is a square
```
       C ------T-----> C'
       |               |
      F i            F' i
       v               v
      D i ---T' i---> D' i
```
commuting up to an isomorphism `e i : T ⋙ F' i ≅ F i ⋙ T' i`, where the functors `F i` are
exact, the functors `T' i` are exact and the exact functors `F' i` jointly reflect
isomorphisms. Then `T` is exact. -/
lemma JointlyReflectIsomorphisms.exactFunctor_of_iso (hP : JointlyReflectIsomorphisms F')
    (T : C ⥤ C') [T.Additive] (T' : ∀ i, D i ⥤ D' i) [∀ i, (T' i).Additive]
    (hT' : ∀ i, exactFunctor _ _ (T' i)) (e : ∀ i, T ⋙ F' i ≅ F i ⋙ T' i) :
    exactFunctor _ _ T := by
  refine ((Functor.exact_tfae T).out 2 4).1 fun S hS ↦ (hP.exact_iff _).2 fun i ↦ ?_
  have : PreservesFiniteLimits (T' i) := (hT' i).1
  have : PreservesFiniteColimits (T' i) := (hT' i).2
  exact (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk ((e i).app _) ((e i).app _)
    ((e i).app _) ((e i).hom.naturality _).symm ((e i).hom.naturality _).symm)).2
      ((hS.map (F i)).map (T' i))

end

variable {C : Type u} [Category.{v} C] {D₁ D₂ : Type u₁} [Category.{v₁} D₁] [Category.{v₁} D₂]

/-- The two-element family of categories `fun b ↦ cond b D₁ D₂` is abelian.

Like `CategoryTheory.instCategoryCond` this is `scoped`, so that it is not tried on
unrelated goals whose head happens to be `cond`. -/
scoped instance instAbelianCond [Abelian D₁] [Abelian D₂] (b : Bool) :
    Abelian (cond b D₁ D₂) :=
  Bool.rec (motive := fun b ↦ Abelian (cond b D₁ D₂)) ‹Abelian D₂› ‹Abelian D₁› b

variable (F₁ : C ⥤ D₁) (F₂ : C ⥤ D₂)

/-- A pair of left exact functors is objectwise left exact. -/
instance preservesFiniteLimits_pairFunctor [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂]
    (b : Bool) : PreservesFiniteLimits (pairFunctor F₁ F₂ b) :=
  Bool.rec (motive := fun b ↦ PreservesFiniteLimits (pairFunctor F₁ F₂ b))
    ‹PreservesFiniteLimits F₂› ‹PreservesFiniteLimits F₁› b

/-- A pair of right exact functors is objectwise right exact. -/
instance preservesFiniteColimits_pairFunctor [PreservesFiniteColimits F₁]
    [PreservesFiniteColimits F₂] (b : Bool) : PreservesFiniteColimits (pairFunctor F₁ F₂ b) :=
  Bool.rec (motive := fun b ↦ PreservesFiniteColimits (pairFunctor F₁ F₂ b))
    ‹PreservesFiniteColimits F₂› ‹PreservesFiniteColimits F₁› b

end CategoryTheory
