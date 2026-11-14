import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.AllField.Representation.Geometric.RefinementDefinitionsSupplement
import Langlands.AllField.Representation.Geometric.RefinementFunctors
/-! Actual normalized induction and Jacquet functors inside product Levis. -/

noncomputable section

open scoped NNReal

namespace Langlands.AllField.Geometric
open Langlands.Geometric
open Langlands.AllField.Geometric

open _root_.CategoryTheory
open Langlands.GeneralLinear

universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

section Topology


end Topology
end Langlands.AllField.Geometric

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open _root_.CategoryTheory
open Langlands.Geometric
open Langlands.AllField.Geometric

universe uF uV uW

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
  (S : BlockRefinement B) {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The actual normalized Jacquet functor of a refinement of a product Levi. -/
def normalizedRefinedJacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedJacquetFunctorOf B S (T.refinedLeviModulus B S)
    (T.isOpen_ker_refinedLeviModulus B S)

/-- The normalized refined induction action uses the positive half of the same modulus. -/
def normalizedRefinedInduced (σ : Representation ℂ (refinedLevi F B S) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    Representation ℂ (B.Levi F)
      (Induction.SmoothFunctions (refinedParabolic F B S)
        (twist (T.refinedParabolicHalfModulus B S)
          (σ.comp (refinedLeviProjection F B S)))) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInducedOf B S (T.refinedLeviHalfModulus B S) σ

/-- The normalized induced map is postcomposition by the original intertwiner. -/
def normalizedRefinedInducedMap
    {σ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (T.normalizedRefinedInduced B S σ).IntertwiningMap
      (T.normalizedRefinedInduced B S τ) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInducedOfMap B S (T.refinedLeviHalfModulus B S) f

/-- Normalized induction between the actual smooth categories of product Levi subgroups. -/
def normalizedRefinedInductionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInductionFunctorOf B S (T.refinedLeviHalfModulus B S)

end Langlands.LocalFieldData
