/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients

/-! # Chern for canonical tower classes

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-chern).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The first-Chern construction at one scheme: the target of integral reduction is
fixed by the Kummer boundary, scalar extension uses the actual ring-object map, and
finite evaluations are concrete finite Kummer arrows.
Source: classes (1)--(2), proof steps 1--8 (blueprint: def-sp-tower-class-chern). -/
structure ChernData (T : Scheme.{u})
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op)) where
  kummer : Kummer l T
  reduction : Reduction T R
  rootModule : Systems T R
  rootForget : reduction.forget.F.obj rootModule ≅ roots l T
  unitIso : reduction.derived.obj
    ((DerivedCategory.singleFunctor (Ab T) 0).obj (integers T)) ≅ unit T R
  rootIso : reduction.derived.obj
      (((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) ≅
    ((DerivedCategory.singleFunctor (Systems T R) 0).obj rootModule)⟦(2 : ℤ)⟧
  scalar : SemilinearSections.ScalarData.{u + 1, u, u + 1} φ
  /-- The unit comparison is fixed by the scalar adjunction, sending one to one. -/
  scalarUnit : scalar.T.obj (unit T R) ≅ unit T A

/-- Specialize the normalized Chern data to the actual quotient coefficient towers.
Source: classes (2) (blueprint: def-sp-tower-class-chern). -/
abbrev Chern (T : Scheme.{u}) :=
  ChernData l T (Rrings l T) (Arings l E T) (coefficientSystemMap l E T)

/-- Normalization of the integral quotient, positive Kummer boundary and unital scalar
extension. These are concrete equalities of derived arrows, separated from the data
record so that elaboration shares the already constructed categories.
Source: classes (2), proof steps 3--8 (blueprint: def-sp-tower-class-chern). -/
def ChernData.Normalized (T : Scheme.{u})
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (c : ChernData l T R A φ)
    (q : coefficient T R ⟶ (SemilinearSections.res.{u + 1, u, u + 1} φ).obj
      (coefficient T A)) : Prop :=
  c.reduction.model.sourceNormalization c.unitIso
    (integerGenerator T R c.reduction.forget) ∧
  c.reduction.model.targetNormalization
    (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
    c.kummer.exact c.rootIso c.rootForget ∧
  unitNormalization c.scalar.T (SemilinearSections.res.{u + 1, u, u + 1} φ)
    c.scalar.adjunction c.scalarUnit q

/-- Specialization of the three normalization equations to the actual ring quotient.
Source: classes (2), proof steps 3--8 (blueprint: def-sp-tower-class-chern). -/
abbrev Chern.Normalized {T : Scheme.{u}} (c : Chern l E T) : Prop :=
  ChernData.Normalized l T (Rrings l T) (Arings l E T)
    (coefficientSystemMap l E T) c (scalarGenerator l E T)

/-- Integral coefficient-linear first Chern class, computed by simultaneous reduction
of the actual constant-tower line-bundle morphism.
Source: classes (2), proof steps 2--8 (blueprint: def-sp-tower-class-chern). -/
def firstChernR {T : Scheme.{u}} (c : Chern l E T) (L : T.Pic) :
    unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj c.rootModule)⟦(2 : ℤ)⟧ :=
  c.unitIso.inv ≫ c.reduction.derived.map (lineBundleClass T L) ≫ c.rootIso.hom

/-- Canonical shift structure of the existing scalar model.
Source: classes (2), derived extension (blueprint: def-sp-tower-class-chern). -/
instance scalarShift {T : Scheme.{u}} (c : Chern l E T) : c.scalar.T.CommShift ℤ :=
  SheafOfModules.sheafScalarModelCommShift (coefficientSystemMap l E T) c.scalar.model

/-- Ordinary scalar extension of the actual root module, with all tower restrictions.
Source: classes (2), coefficient extension (blueprint: def-sp-tower-class-chern). -/
def lineModule {T : Scheme.{u}} (c : Chern l E T) : Systems T (Arings l E T) :=
  c.scalar.model.E.obj c.rootModule

/-- The Tate line placed in degree zero.
Source: classes (2) (blueprint: def-sp-tower-class-chern). -/
def line {T : Scheme.{u}} (c : Chern l E T) : D T (Arings l E T) :=
  (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj (lineModule l E c)

/-- The canonical derived-to-ordinary scalar-extension comparison on the root module.
It is the universal derived counit with the standard single-complex comparisons.
Source: classes (2), K-flat target identification (blueprint: def-sp-tower-class-chern). -/
def lineComparison {T : Scheme.{u}} (c : Chern l E T) :
    c.scalar.T.obj ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
      c.rootModule) ⟶ line l E c :=
  c.scalar.T.map
      ((DerivedCategory.singleFunctorIsoCompQ (Systems T (Rrings l T)) 0).hom.app
        c.rootModule) ≫
    c.scalar.model.ε.app
      ((HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0).obj c.rootModule) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex c.scalar.model.E (.up ℤ) 0).hom.app
        c.rootModule) ≫
    (DerivedCategory.singleFunctorIsoCompQ (Systems T (Arings l E T)) 0).inv.app
      (lineModule l E c)

/-- The inverse line is the internal sheaf Hom into the actual coefficient unit
on the same ringed sequence site, not an unspecified inverse object.
Source: classes preamble, definition-tate-twists negative powers
(blueprint: def-sp-tower-class-chern). -/
def inverseLineModule {T : Scheme.{u}} (c : Chern l E T) : Systems T (Arings l E T) :=
  SheafOfModules.homObj (R := SemilinearSections.systemRing.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
    (lineModule l E c) (coefficient T (Arings l E T))

/-- The inverse Tate line in degree zero.
Source: classes (4) (blueprint: def-sp-tower-class-chern). -/
def inverseLine {T : Scheme.{u}} (c : Chern l E T) : D T (Arings l E T) :=
  (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj
    (inverseLineModule l E c)

/-- The coefficient-linear first Chern morphism is the actual scalar extension
of the integral reduction of the line-bundle class, followed by the universal
K-flat target comparison. No free first-Chern arrow is part of the data.
Source: classes (2), proof steps 2--8 (blueprint: def-sp-tower-class-chern). -/
def firstChern {T : Scheme.{u}} (c : Chern l E T) (L : T.Pic) :
    unit T (Arings l E T) ⟶ (line l E c)⟦(2 : ℤ)⟧ :=
  c.scalarUnit.inv ≫ c.scalar.T.map (firstChernR l E c L) ≫
    (c.scalar.T.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj c.rootModule) ≫
    (lineComparison l E c)⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
