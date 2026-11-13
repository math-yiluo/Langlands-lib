import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Rational.LatticeStabilizerBoundedness
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Smooth integral models of maximal algebraically bounded subgroups -/

noncomputable section

universe u

open AlgebraicGeometry ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The maximal-bounded-subgroup step in KP Proposition 8.3.1, stated for the
original affine group and its actual rational-point subgroup. -/
def MaximalBoundedIntegralModelStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [IsDiscreteValuationRing (valuation K).integer]
    [HenselianLocalRing (valuation K).integer]
    [IsAlgClosed (IsLocalRing.ResidueField (valuation K).integer)]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left],
    Smooth G.X.hom →
    ∀ B : Subgroup (rationalPoints G),
      Maximal (fun C : Subgroup (rationalPoints G) =>
        IsAlgebraicallyBounded K G.X (C : Set (rationalPoints G))) B →
      ∃ M : IntegralModel (valuation K).integer K G,
        M.IsSmooth ∧ M.integralPoints = B

end Langlands.GroupScheme
