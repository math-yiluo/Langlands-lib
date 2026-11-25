/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation
import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Ordinary localization in the fixed constant coefficient coordinates

Source: Stacks 09AH and 09BM; blueprint operations proof (2c)
(blueprint: lem-sp-tower-ordinary-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section Transport

variable {C C' U U' Z Z' : Type*}
  [Category* C] [Category* C'] [Category* U] [Category* U']
  [Category* Z] [Category* Z']

private def unit_comparison {L : C ⥤ Z} {R : Z ⥤ C}
    {L' : C ⥤ Z} {R' : Z ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ R') :
    L ⋙ R ≅ L' ⋙ R' :=
  Functor.isoWhiskerLeft L e ≪≫
    Functor.isoWhiskerRight ((a.ofNatIsoRight e).leftAdjointUniq a') R'

end Transport

attribute [local irreducible] sfIntrinsicModuleEquivalence

end AlgebraicGeometry.ProEtale.SpTowerShriek
