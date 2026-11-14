import Langlands.AllFieldBZ.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof
import Langlands.AllFieldBZ.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Geometric.PadicCorrectionCancellationProof

/-!
# All-field port of `Langlands.Representation.Geometric.PadicCorrectionCancellationProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.PadicCorrectionCancellationProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped BigOperators
open scoped NNReal
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar padicStandardIntersectionsTheorem
private theorem _root_.Langlands.Geometric.prod_subtype_eq_prod_ite
    {ι A : Type*} [Fintype ι] [CommMonoid A]
    (p : ι → Prop) [DecidablePred p] (a : ι → A) :
    (∏ i : {i // p i}, a i) = ∏ i, if p i then a i else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) a).symm

namespace General
open Langlands.Geometric.General
end General
universe uF

end Langlands.AllFieldBZ.Geometric
