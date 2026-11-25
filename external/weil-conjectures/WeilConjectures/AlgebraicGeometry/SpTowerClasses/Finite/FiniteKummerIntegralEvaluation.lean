/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralTowerBoundary
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralRootClass
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralLineClassEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralBoundaryEvaluationMap
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteComparedKummerBoundary

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-kummer-integral-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- Evaluation of the integral tower Kummer class is the comparison image of the
etale Kummer class. Source: Stacks 03PL; diagonal-tower trace (1).
(blueprint: lem-sfb-finite-kummer-integral-evaluation).

Proof: write the line bundle class as the exact comparison image of its Picard
extension, transported along integerComparison and cartierUnitsComparison.
Exact evaluation of constant towers is the identity functor. The morphism from
the comparison image of the etale Kummer sequence to the evaluated tower Kummer
sequence has units comparison in its middle and final terms and roots comparison
in its first term. Its squares are the defining kernel equation and compatibility
of the additive units comparison with multiplication by the exponent. Naturality
of the extension class, followed by associativity of Yoneda composition, identifies
the evaluated composite with the image of Picard class composed with the etale
Kummer extension. This is exactly kummerδ₁. Realize the resulting Ext equality in
the derived category. The argument uses positive exponents and covers zero classes
and empty schemes without a separate case. -/
theorem finiteKummer_integral_evaluation (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (L : T.Pic) :
    finiteEvaluatedIntegralBoundary l T k n L =
      finiteIntegralRootClass l T n
        (T.kummerδ₁ (l ^ (n + 1)) hT (Scheme.Pic.toCohomologicalPicardGroup T L)) := by
  rw [finiteIntegralBoundary_evaluation_map, finiteIntegralLineClass_evaluation]
  exact finiteComparedKummerBoundary l T k n hT L

end AlgebraicGeometry.ProEtale.SpTowerClasses
