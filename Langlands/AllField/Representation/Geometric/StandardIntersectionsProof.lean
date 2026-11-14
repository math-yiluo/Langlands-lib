import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.WeylStatementSupplement
namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding PadicStandardIntersectionsTheorem padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe u

variable {n : ℕ}

variable (R : Type u) [CommRing R]

/-- The exact published two-sided p-adic standard-intersection statement. -/
theorem padicStandardIntersectionsTheorem :
    PadicStandardIntersectionsTheorem.{u} := by
  intro F _ n hn B C w
  constructor
  · exact exists_standardIntersections F B C w.val
      w.property.1
  · exact exists_standardIntersections F C B w.val⁻¹
      w.property.2

end Langlands.AllField.Geometric
