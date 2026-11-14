import Langlands.AllFieldBZ.Group.GL.UpperBruhatPivotProof
import Langlands.AllFieldBZ.Representation.Geometric.BruhatMatrixStatement
import Langlands.Representation.Geometric.BruhatMatrixExistenceProof

/-!
# All-field port of `Langlands.Representation.Geometric.BruhatMatrixExistenceProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.BruhatMatrixExistenceProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem padicBruhatMatrixExistence
open Langlands.GeneralLinear
universe u

/-- Every p-adic parabolic double coset has an inverse permutation-matrix representative. -/
theorem padicBruhatMatrixExistence : PadicBruhatMatrixExistenceTheorem.{u} := by
  intro F n _ B C g
  obtain ⟨a, b, w, ha, hb, hg⟩ := fieldUpperBruhatFactorizationTheorem F.Carrier n g
  exact ⟨w⁻¹, inverse_permutation_doubleCoset_of_upper_factorization B C g a b w ha hb hg⟩

end Langlands.AllFieldBZ.Geometric
