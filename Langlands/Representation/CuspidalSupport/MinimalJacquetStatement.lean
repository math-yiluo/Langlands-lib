import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Jacquet.Parabolic

/-! Nonzero quasicuspidal Jacquet descent from BZ77 section 2.14(1). -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

/-- Every nonzero smooth representation of an actual p-adic general linear
 group has a nonzero quasicuspidal normalized Jacquet module for some standard
 block parabolic. All natural ranks, including zero, are included. -/
def MinimalNonzeroJacquetTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    letI := T.topology
    letI := T.generalLinearTopology n
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      Nontrivial A → ∃ B : BlockShape n,
        let J := (T.normalizedJacquetFunctor B).obj A
        Nontrivial J ∧ IsLeviQuasicuspidal B J.representation

end Langlands.CuspidalSupport
