/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The preadditive coyoneda functor along adjunctions and fully faithful functors

For an adjunction `F ⊣ G` of additive functors between preadditive categories, the functor
`Y ↦ Hom(F X, Y)` (with values in abelian groups) is `Y ↦ Hom(X, G Y)`
(`CategoryTheory.Adjunction.preadditiveCoyonedaObjIso`). For a fully faithful additive functor
`F`, the functor `Y ↦ Hom(X, Y)` is `Y ↦ Hom(F X, F Y)`
(`CategoryTheory.Functor.FullyFaithful.preadditiveCoyonedaObjIso`).

For a ring `R`, a morphism `R ⟶ M` of `R`-modules is determined by the image of `1`, so that the
functor `M ↦ Hom(R, M)` to abelian groups is the forgetful functor
(`ModuleCat.preadditiveCoyonedaObjSelfIso`).
-/

@[expose] public section

universe v u₁ u₂

open Opposite

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D] [Preadditive C]
  [Preadditive D]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive]

/-- For an adjunction `F ⊣ G` of additive functors, the functor `Y ↦ Hom(F X, Y)` to abelian
groups is isomorphic to `Y ↦ Hom(X, G Y)`. -/
noncomputable def preadditiveCoyonedaObjIso (X : C) :
    preadditiveCoyoneda.obj (op (F.obj X)) ≅ G ⋙ preadditiveCoyoneda.obj (op X) :=
  NatIso.ofComponents (fun Y ↦ (adj.homAddEquiv X Y).toAddCommGrpIso)
    (fun g ↦ by
      ext f
      exact adj.homEquiv_naturality_right f g)

end Adjunction

namespace Functor.FullyFaithful

variable {F : C ⥤ D} (hF : F.FullyFaithful) [F.Additive]

/-- For a fully faithful additive functor `F`, the functor `Y ↦ Hom(X, Y)` to abelian groups is
isomorphic to `Y ↦ Hom(F X, F Y)`. -/
noncomputable def preadditiveCoyonedaObjIso (X : C) :
    preadditiveCoyoneda.obj (op X) ≅ F ⋙ preadditiveCoyoneda.obj (op (F.obj X)) :=
  NatIso.ofComponents
    (fun Y ↦ (AddEquiv.ofBijective (F.mapAddHom (X := X) (Y := Y))
      (hF.map_bijective X Y)).toAddCommGrpIso)
    (fun g ↦ by
      ext f
      exact F.map_comp f g)

end Functor.FullyFaithful

end CategoryTheory

open CategoryTheory

namespace ModuleCat

variable (R : Type v) [Ring R]

/-- Morphisms `R ⟶ M` of `R`-modules are the elements of `M`, by evaluation at `1`. -/
def selfHomAddEquiv (M : ModuleCat.{v} R) : (ModuleCat.of R R ⟶ M) ≃+ M where
  toFun f := f.hom 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
  left_inv f := by
    ext
    simp
  right_inv x := by simp
  map_add' _ _ := rfl

/-- The functor `M ↦ Hom(R, M)` from `R`-modules to abelian groups is the forgetful functor. -/
def preadditiveCoyonedaObjSelfIso :
    preadditiveCoyoneda.obj (op (ModuleCat.of R R)) ≅ forget₂ (ModuleCat.{v} R) AddCommGrpCat :=
  NatIso.ofComponents (fun M ↦ (selfHomAddEquiv R M).toAddCommGrpIso)
    (fun g ↦ by
      ext f
      rfl)

end ModuleCat
