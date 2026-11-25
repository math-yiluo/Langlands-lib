/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ComplexFunctorSquare

/-! # Evaluation of a quotient-tower complex with explicit complex endpoints

Source: Stacks Tags 0940, 0941 and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)

/-- Ordinary finite evaluation retains the quotient scalar action.
Source: Stacks Tags 0940 and 099M
(blueprint: lem-sf-quotient-tower-evaluation-complex). -/
def quotientEvaluationIso :
    reductionTower J A I false ⋙ (evaluation ℕᵒᵖ (Mod (constant J A))).obj (op n) ≅
      change (quotient J A I n) ⋙ res (quotient J A I n) :=
  Iso.refl _

/-- Finite evaluation with both iterated complex functors visible in its type.
Source: Stacks Tags 0941 and 099M
(blueprint: lem-sf-quotient-tower-evaluation-complex). -/
@[irreducible]
def quotientEvaluationComplexIso :
    (reductionTower J A I false).mapHomologicalComplex (.up ℤ) ⋙
        ((evaluation ℕᵒᵖ (Mod (constant J A))).obj (op n)).mapHomologicalComplex (.up ℤ) ≅
      (change (quotient J A I n)).mapHomologicalComplex (.up ℤ) ⋙
        (res (quotient J A I n)).mapHomologicalComplex (.up ℤ) :=
  mapComplexSquare (reductionTower J A I false)
    ((evaluation ℕᵒᵖ (Mod (constant J A))).obj (op n))
    (change (quotient J A I n)) (res (quotient J A I n))
    (quotientEvaluationIso J A I n)

end CategoryTheory.ConstantCompletion
