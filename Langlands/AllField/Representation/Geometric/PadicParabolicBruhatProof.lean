import Langlands.Representation.Geometric.PadicParabolicBruhatProof
import Langlands.AllField.Representation.Geometric.BruhatMatrixExistenceProof
import Langlands.AllField.Representation.Geometric.BruhatWeylReflectionProof
import Langlands.AllField.Representation.Geometric.WeylStatement
namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem PadicParabolicBruhatTheorem padicBruhatMatrixExistence padicBruhatWeylReflection padicParabolicBruhat
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe u

/-- Minimal permutations parametrize the actual local-field parabolic double cosets
by their inverse permutation matrices. -/
theorem padicParabolicBruhat : PadicParabolicBruhatTheorem.{u} := by
  intro F _ n hn B C
  exact parabolicDoubleCoset_bijective_of_matrix_conditions F B C
    (weylMinimalRepresentativeTheorem n hn B C)
    (padicBruhatMatrixExistence F n hn B C)
    (padicBruhatWeylReflection F n hn B C)

end Langlands.AllField.Geometric
