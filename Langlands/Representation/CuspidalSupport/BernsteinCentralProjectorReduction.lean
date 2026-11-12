import Langlands.Representation.Category.DecompositionCentralProjectors
import Langlands.Representation.CuspidalSupport.BernsteinCentralIdempotentStatements
import Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements

/-! # The central-idempotent consequence of the Bernstein decomposition -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.Aubert.General.RationalPointFamily
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.4, first paragraph, reduced to the published VI.7.2 decomposition target. -/
theorem bernsteinCentralIdempotent_of_decomposition
    (h : BernsteinDecompositionStatement.{uF, uV}) :
    BernsteinCentralIdempotentStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family
  classical
  let hd := h F G T i ν family
  refine ⟨SmoothRep.centralProjector hd, ?_, ?_, ?_, ?_⟩
  · exact SmoothRep.centralProjector_idempotent hd
  · intro s V hV
    exact SmoothRep.centralProjector_app_of_mem hd s V hV
  · intro s t hst V hV
    exact SmoothRep.centralProjector_app_of_ne hd s t (Ne.symm hst) V hV
  · exact SmoothRep.centralProjector_finite_sum hd

end Langlands.CuspidalSupport
