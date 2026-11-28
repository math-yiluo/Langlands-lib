import Langlands.Global.AdelicSpaceSpreadMapStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedStructuralFibres

/-! # Compactness and stabilization for proper algebraic spaces -/

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- For a proper algebraic space over a global function field, its adelic points are compact
and every sufficiently large stage of a separated finite-type model gives the full space. -/
def CurvePlaceSpaceProperStabilizationStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)), S.Nonempty →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))),
      IsSeparated X → FiniteTypeOverRing (curvePlaceSIntegers k F S) X →
      ∀ (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
        (e : curvePlaceSpaceGenericFiber k F S X ≅ Y),
        IsProperMorphism (structuralMorphism Y) →
        letI := curvePlaceSpaceSpreadTopology k F S X Y e
        CompactSpace (CurvePlaceSpaceFieldAdelePoints k F Y) ∧
          ∃ T : AdelicLevelIndexAbove S, ∀ U : AdelicLevelIndexAbove S, T ≤ U →
            letI := curvePlaceSpaceStageTopology k F S X U
            IsHomeomorph
              (curvePlaceSpaceSpreadEquiv k F S X Y e ∘ curvePlaceSpaceStageMap k F S X U)

/-- For a proper algebraic space over a number field, its full adelic points are compact
and every sufficiently large stage of a separated finite-type model gives the full space. -/
def NumberFieldSpaceProperStabilizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))),
    IsSeparated X → FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X →
    ∀ (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
      (e : numberFieldSpaceGenericFiber K S X ≅ Y),
      IsProperMorphism (structuralMorphism Y) →
      letI := numberFieldSpaceSpreadTopology K S X Y e
      CompactSpace (NumberFieldSpaceFieldAdelePoints K Y) ∧
        ∃ T : AdelicLevelIndexAbove S, ∀ U : AdelicLevelIndexAbove S, T ≤ U →
          letI := numberFieldSpaceStageTopology K S X U
          IsHomeomorph
            (numberFieldSpaceSpreadEquiv K S X Y e ∘ numberFieldSpaceStageMap K S X U)

/-- The compactness and stabilization consequences of Proposition 4.4 for algebraic spaces,
as extended on p. 17 of Conrad's adelic points paper. -/
def AdelicSpaceProperStabilizationStatement : Prop :=
  CurvePlaceSpaceProperStabilizationStatement.{u} ∧
    NumberFieldSpaceProperStabilizationStatement.{u}

end Langlands.Global
