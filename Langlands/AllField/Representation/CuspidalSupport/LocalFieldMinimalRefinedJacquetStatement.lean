import Langlands.AllField.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.CuspidalSupport.LeviDefinitions

/-! Nonzero quasicuspidal refined Jacquet descent on a matrix Levi. -/

namespace Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear Langlands.Geometric
open Langlands.CuspidalSupport (IsLeviQuasicuspidal)

universe uF uV

/-- Every nonzero smooth object of a matrix Levi has a nonzero refined
Jacquet module which is quasicuspidal on the flattened Levi. -/
def LocalFieldMinimalRefinedJacquetStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)), Nontrivial A →
      ∃ S : BlockRefinement B,
        Nontrivial (RefinedJacquetModule B S A.representation) ∧
          IsLeviQuasicuspidal (B.flatten S)
            ((T.normalizedRefinedJacquet B S A.representation).comp
              (flattenedLeviEquiv F B S).toMonoidHom)

end Langlands.AllField.CuspidalSupport
