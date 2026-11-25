/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern

/-! # The scalar counit on degree-zero module systems

Source: blueprint classes proof (2), derived-to-ordinary scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The universal scalar counit restricted to singles. Its component at the root
module is exactly `lineComparison`.
Source: classes (2), scalar realization (blueprint: def-sp-tower-scalar-single-counit). -/
def scalarSingleCounit {T : Scheme.{u}} (c : Chern l E T) :
    DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0 ⋙ c.scalar.T ⟶
      c.scalar.model.E ⋙ DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0 :=
  Functor.whiskerRight
      (DerivedCategory.singleFunctorIsoCompQ (Systems T (Rrings l T)) 0).hom c.scalar.T ≫
    Functor.whiskerLeft (HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0)
      c.scalar.model.ε ≫
    Functor.whiskerRight
      (HomologicalComplex.singleMapHomologicalComplex c.scalar.model.E (.up ℤ) 0).hom
        DerivedCategory.Q ≫
    Functor.whiskerLeft c.scalar.model.E
      (DerivedCategory.singleFunctorIsoCompQ (Systems T (Arings l E T)) 0).inv

end AlgebraicGeometry.ProEtale.SpTowerClasses
