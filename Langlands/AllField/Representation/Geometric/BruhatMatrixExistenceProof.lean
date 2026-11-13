import Langlands.Representation.Geometric.BruhatMatrixExistenceProof
import Langlands.AllField.Representation.Geometric.BruhatMatrixStatement
namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem padicBruhatMatrixExistence
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe u

/-- Every local-field parabolic double coset has an inverse permutation-matrix representative. -/
theorem padicBruhatMatrixExistence : PadicBruhatMatrixExistenceTheorem.{u} := by
  intro F _ n _ B C g
  obtain ⟨a, b, w, ha, hb, hg⟩ := fieldUpperBruhatFactorizationTheorem F n g
  exact ⟨w⁻¹, inverse_permutation_doubleCoset_of_upper_factorization B C g a b w ha hb hg⟩

end Langlands.AllField.Geometric
