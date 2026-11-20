import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-! # A necessary exponent bound for unitarity of a real rank-two principal series -/

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- The real part of the exponent difference in an infinitesimally unitarizable
principal series of two real characters has absolute value less than one.
It vanishes if the characters have opposite parity. -/
def RealGLTwoPrincipalSeriesUnitaryBoundStatement : Prop :=
  ∀ c d : RealCharacterData,
    IsRealUnitarizableGKModule 2
        (realStandardRep 2 [.character c, .character d])
        (realStandardLie 2 [.character c, .character d]) →
      |(c.exponent - d.exponent).re| < 1 ∧
        (c.parity ≠ d.parity → (c.exponent - d.exponent).re = 0)

end Langlands.Archimedean
