import Langlands.Representation.Geometric.BruhatWeylReflectionProof
import Langlands.AllField.Representation.Geometric.BruhatMatrixStatement
/-! Reflection of Weyl double cosets using a nonzero determinant term. -/

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem padicBruhatWeylReflection
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe u

variable {n : ℕ} {R : Type u} [CommRing R] [Nontrivial R]

/-- The exact published local-field reflection proposition. -/
theorem padicBruhatWeylReflection : PadicBruhatWeylReflectionTheorem.{u} := by
  intro F _ n hn B C v w h
  exact weyl_doubleCoset_eq_of_inverse_permutation_eq B C h

end Langlands.AllField.Geometric
