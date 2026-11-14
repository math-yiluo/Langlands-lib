import Langlands.AllFieldBZ.Representation.Geometric.BruhatMatrixExistenceProof
import Langlands.AllFieldBZ.Representation.Geometric.BruhatWeylReflectionProof
import Langlands.AllFieldBZ.Representation.Geometric.WeylStatement
import Langlands.AllFieldBZ.Representation.Geometric.WeylUniquenessProof
import Langlands.Representation.Geometric.PadicParabolicBruhatProof

/-!
# All-field port of `Langlands.Representation.Geometric.PadicParabolicBruhatProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.PadicParabolicBruhatProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem padicBruhatMatrixExistence padicBruhatWeylReflection padicParabolicBruhat
open Langlands.GeneralLinear
universe u

/-- Minimal permutations parametrize the actual p-adic parabolic double cosets
by their inverse permutation matrices. -/
theorem padicParabolicBruhat : PadicParabolicBruhatTheorem.{u} := by
  intro F n hn B C
  exact parabolicDoubleCoset_bijective_of_matrix_conditions F.Carrier B C
    (weylMinimalRepresentativeTheorem n hn B C)
    (padicBruhatMatrixExistence F n hn B C)
    (padicBruhatWeylReflection F n hn B C)

end Langlands.AllFieldBZ.Geometric
