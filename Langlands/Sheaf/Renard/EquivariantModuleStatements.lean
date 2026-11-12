import Langlands.Sheaf.Renard.CompactSectionActions
import Langlands.Sheaf.Renard.ProjectorActionSheaf
import Langlands.Sheaf.Renard.SmoothProjectorActionSheaf
import Mathlib.CategoryTheory.Equivalence

/-! # Renard III.3: the actual equivariant sheaf and test-module equivalences -/

namespace Langlands.Sheaf.Renard.EquivariantModuleStatements

open CategoryTheory
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.CompatibleTestActions

universe uG

/-- The III.3.1 identification uses exactly the original compact-section and
original equivariant projector-sheaf functors, including all their maps. -/
def AlgebraicStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (_hG : Langlands.Topology.IsLocallyProfinite G)
    (X : Type) [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (hX : Langlands.Topology.IsLocallyProfinite X),
    ∃ e : ActionSheaf G X ≌ CompatibleTestAction.{uG, 0, 0} G X,
      e.functor = CompactSectionActions.functor hX ∧
      e.inverse = ProjectorActionSheaf.functor hX

/-- Restricting the same actual correspondence to whole-module smoothness gives
the smooth categories used in III.3.2, without taking smooth vectors. -/
def SmoothStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : Langlands.Topology.IsLocallyProfinite G)
    (X : Type) [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (hX : Langlands.Topology.IsLocallyProfinite X),
    ∃ e : SmoothActionSheaf G X ≌
        CompactSectionActions.SmoothCompatibleTestAction (G := G) (X := X),
      e.functor = CompactSectionActions.smoothFunctor hX ∧
      e.inverse = SmoothProjectorActionSheaf.smoothFunctor hX hG

/-- The original-action identification and its whole-module smooth restriction. -/
def Statements : Prop := AlgebraicStatement.{uG} ∧ SmoothStatement.{uG}

end Langlands.Sheaf.Renard.EquivariantModuleStatements
