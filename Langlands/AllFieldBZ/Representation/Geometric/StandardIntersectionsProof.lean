import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.AllFieldBZ.Representation.Geometric.MonotoneBlocksProof
import Langlands.Representation.Geometric.StandardIntersectionsProof

/-!
# All-field port of `Langlands.Representation.Geometric.StandardIntersectionsProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.StandardIntersectionsProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem padicStandardIntersectionsTheorem
open Langlands.GeneralLinear
universe u

variable {n : ℕ}

variable (R : Type u) [CommRing R]

/-- The exact published two-sided p-adic standard-intersection statement. -/
theorem padicStandardIntersectionsTheorem :
    PadicStandardIntersectionsTheorem.{u} := by
  intro F n hn B C w
  constructor
  · exact exists_standardIntersections F.Carrier B C w.val
      w.property.1
  · exact exists_standardIntersections F.Carrier C B w.val⁻¹
      w.property.2

end Langlands.AllFieldBZ.Geometric
