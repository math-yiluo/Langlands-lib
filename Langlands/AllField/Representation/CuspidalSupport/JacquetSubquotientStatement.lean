import Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
/-! Algebraic interfaces for carrying actual subquotients through Jacquet descent. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding NormalizedJacquetSubquotientTheorem
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear

universe uF uV uW

/-- The actual normalized Jacquet functor preserves actual subquotients. -/
def NormalizedJacquetSubquotientTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
      SmoothRep.IsSubquotient D A →
      SmoothRep.IsSubquotient ((T.normalizedJacquetFunctor B).obj D)
        ((T.normalizedJacquetFunctor B).obj A)

end Langlands.AllField.CuspidalSupport
