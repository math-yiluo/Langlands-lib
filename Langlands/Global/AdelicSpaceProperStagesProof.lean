import Langlands.Global.AdelicSpaceProperStagesReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalFieldProperPointMapProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.TopologicalMorphismBaseChange

/-! # Proper adelic stages and their exact full-adele preimages -/

universe u

open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- Proper algebraic-space model morphisms induce proper maps on every adelic stage,
with exact full-adele preimages of the stage ranges, in both arithmetic cases. -/
theorem adelicSpaceProperStages : AdelicSpaceProperStagesStatement.{u} :=
  adelicSpaceProperStages_of_inputs localFieldProperPointMap spaceValuativeExistence
    (fun _ _ _ _ _ _ hf => hf.baseChangeMap)

end Langlands.Global
