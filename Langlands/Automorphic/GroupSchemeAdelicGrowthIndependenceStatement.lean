import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth

/-! # Closed-embedding independence of full adelic growth conditions -/

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- Changing a positive-rank closed matrix embedding preserves the existing
ordinary and uniform full adelic growth predicates on their original carriers.
The uniform comparisons use the same smooth atlas and actual enveloping action. -/
def ClosedImmersionAdelicGrowthIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (N M : ℕ)
    (rho : GroupScheme.MatrixRepresentation G (Fin N))
    (sigma : GroupScheme.MatrixRepresentation G (Fin M)),
    0 < N → 0 < M →
      GroupScheme.IsClosedSubgroup rho → GroupScheme.IsClosedSubgroup sigma →
      (∀ f : ContinuousRationalFunctions F G,
        (HasAdelicModerateGrowth F G rho f ↔ HasAdelicModerateGrowth F G sigma f) ∧
        (HasAdelicPolynomialGrowth F G rho f ↔
          HasAdelicPolynomialGrowth F G sigma f)) ∧
      (∀ (d : ℕ) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth)
        (f : FinitePlotSmoothRationalFunctions F G),
        (HasAdelicUniformModerateGrowth F G rho hsmooth hcalc f ↔
          HasAdelicUniformModerateGrowth F G sigma hsmooth hcalc f) ∧
        (HasAdelicUniformPolynomialGrowth F G rho hsmooth hcalc f ↔
          HasAdelicUniformPolynomialGrowth F G sigma hsmooth hcalc f))

end Langlands.Automorphic.GroupSchemeFunctions
