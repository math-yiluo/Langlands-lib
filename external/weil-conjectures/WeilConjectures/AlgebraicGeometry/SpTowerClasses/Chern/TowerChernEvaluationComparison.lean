/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarChernArrow

/-! # Evaluation of the scalar first Chern construction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Evaluating and forgetting the scalar arrow recovers evaluatedChern.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: lem-sfb-chern-evaluation-comparison).
Proof: expand the constructed scalar arrow and successive exact-functor arrow
transports. These are precisely firstChern followed by evaluatedChern and the
finite forgetful functor. All endpoints and comparison maps agree definitionally;
HEq records this identity without expanding their type transports downstream. -/
theorem forgetEvaluatedArrow_firstChernR (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T) (L : T.Pic) (n : ℕ) :
    HEq (forgetEvaluatedArrow (C := Systems T (Arings l E T))
      (SpTowerShriek.ev l E T n) (finiteForget l E T n) (lineEvaluation l E c n)
      (scalarChernArrow l E c (firstChernR l E c L)))
      (mapSingleArrow (finiteForget l E T n) (2 : ℤ) (evaluatedChern l E c L n)) := by
  rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
