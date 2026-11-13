import Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
import Langlands.AllField.Representation.Jacquet.Parabolic
/-! Nonzero quasicuspidal Jacquet descent from BZ77 section 2.14(1). -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding MinimalNonzeroJacquetTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV

/-- Every nonzero smooth representation of an actual local-field general linear
 group has a nonzero quasicuspidal normalized Jacquet module for some standard
 block parabolic. All natural ranks, including zero, are included. -/
def MinimalNonzeroJacquetTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ),
    letI := T.topology
    letI := T.generalLinearTopology n
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
      Nontrivial A → ∃ B : BlockShape n,
        let J := (T.normalizedJacquetFunctor B).obj A
        Nontrivial J ∧ IsLeviQuasicuspidal B J.representation

end Langlands.AllField.CuspidalSupport
