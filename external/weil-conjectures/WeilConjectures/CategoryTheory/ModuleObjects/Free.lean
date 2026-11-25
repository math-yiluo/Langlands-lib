/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!

# Free and finitely presented module objects

Let `C` be an abelian monoidal category whose tensor product is additive in each variable, and
`R : C` an algebra object such that `R ⊗ -` is right exact, so that `Mod C R` is abelian.

* `Mod.finiteFree R n` is the finiteFree module `R^n = R ⊕ ⋯ ⊕ R` of rank `n`.
* `Mod.IsFree R M`: `M` is isomorphic to `R^n` for some `n`.
* `Mod.IsFinitelyPresented R M`: `M` is isomorphic to the cokernel of a morphism
  `R^m ⟶ R^n` between free modules of finite rank.
* `Mod.freeFunctor R : C ⥤ Mod C R` is the free module functor `M ↦ R ⊗ M`, for any monoid
  object `R` of a monoidal category.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

section Abelian

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  (R : C) [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- The finiteFree module object of rank `n`. -/
noncomputable abbrev finiteFree (n : ℕ) : Mod C R :=
  ⨁ fun _ : Fin n ↦ regular R

/-- A module object is *locally finiteFree of rank `n`* in the trivial (global) sense if it is
isomorphic to `R^n`; see the geometric files for the local version. -/
def IsFree (M : Mod C R) : Prop :=
  ∃ n : ℕ, Nonempty (M ≅ finiteFree R n)

/-- A module object is *finitely presented* if it is isomorphic to the cokernel of a morphism
`R^m ⟶ R^n` between finiteFree modules of finite rank. -/
def IsFinitelyPresented (M : Mod C R) : Prop :=
  ∃ (n m : ℕ) (f : finiteFree R m ⟶ finiteFree R n), Nonempty (M ≅ cokernel f)

end Abelian

section FreeFunctor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (R : C) [MonObj R]

open MonObj

/-- The free module object functor `M ↦ R ⊗ M`, left adjoint to the forgetful functor. -/
@[simps]
def freeFunctor : C ⥤ Mod C R where
  obj M := { X := R ⊗ M, mod := freeModObj R M }
  map {M N} f :=
    letI := freeModObj R M
    letI := freeModObj R N
    { hom := R ◁ f
      isModHom := ⟨by
        change ((α_ R R M).inv ≫ μ ▷ M) ≫ R ◁ f = R ◁ (R ◁ f) ≫ (α_ R R N).inv ≫ μ ▷ N
        rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc]⟩ }

end FreeFunctor

end CategoryTheory.Mod
