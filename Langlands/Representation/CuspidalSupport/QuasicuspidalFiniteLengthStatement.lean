import Langlands.LocalField.Definitions
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Mathlib.RingTheory.FiniteLength

/-!
# Finite length of finitely generated admissible quasicuspidal Levi representations

The cuspidal subcase of the finite-type finite-length argument of Silberger
(1979), Theorem 5.4.1.6, on actual standard product Levis, with the elementary
empty-product extension. This module defines a proposition; it does not prove it.
-/

namespace Langlands.CuspidalSupport

universe uF uV

/-- Every admissible finitely generated quasicuspidal representation of an actual
standard product Levi has finite length over its group algebra. All ranks,
including zero, and independent field and representation universes are retained. -/
def LeviQuasicuspidalFiniteLengthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      A.IsAdmissible →
      IsLeviQuasicuspidal B A.representation →
      Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier)) A.representation.asModule →
      IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier)) A.representation.asModule

end Langlands.CuspidalSupport
