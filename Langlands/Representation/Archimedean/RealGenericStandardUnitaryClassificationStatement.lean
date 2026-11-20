import Langlands.Representation.Archimedean.RealGenericUnitaryInducingData
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-! # The real generic unitary classification on irreducible standard modules -/

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- An irreducible infinitesimally unitary standard module of `GLₙ(ℝ)` admits a standard
parameter formed from unitary discrete blocks and complementary pairs. -/
def RealGenericStandardUnitaryClassificationStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) →
    ∃ es : List RealBlock, IsRealGenericUnitaryInducingData es ∧
      HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es

end Langlands.Archimedean
