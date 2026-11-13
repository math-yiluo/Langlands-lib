import Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement
import Langlands.AllField.Group.GL.Padic
/-!
# Finite length of finitely generated admissible quasicuspidal Levi representations

The cuspidal subcase of the finite-type finite-length argument of Silberger
(1979), Theorem 5.4.1.6, on actual standard product Levis, with the elementary
empty-product extension. This module defines a proposition; it does not prove it.
-/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviQuasicuspidalFiniteLengthStatement
open Langlands.AllField.CuspidalSupport

universe uF uV

/-- Every admissible finitely generated quasicuspidal representation of an actual
standard product Levi has finite length over its group algebra. All ranks,
including zero, and independent field and representation universes are retained. -/
def LeviQuasicuspidalFiniteLengthStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F),
      A.IsAdmissible →
      IsLeviQuasicuspidal B A.representation →
      Module.Finite (MonoidAlgebra ℂ (B.Levi F)) A.representation.asModule →
      IsFiniteLength (MonoidAlgebra ℂ (B.Levi F)) A.representation.asModule

end Langlands.AllField.CuspidalSupport
