import Langlands.Automorphic.CuspidalArchimedeanComponentStatement
import Langlands.Representation.Archimedean.RealStandardKTypeMultiplicityOneStatement

/-!
# Reduction of archimedean irreducibility to a multiplicity-one `O(n)`-type

`CuspidalArchimedeanStandardIrreducibleStatement` says that a standard module which is the
parameter of an actual cuspidal realization at an infinite place is irreducible. This module
states that it follows from `Archimedean.RealStandardKTypeMultiplicityOneStatement` (a
multiplicity-one `O(n)`-type in every real standard module).

The reduction is internal to this project; it is not a statement from the literature. The
intended argument: at an infinite place the realization is a sum of copies of one irreducible
component (it is irreducible, and the images of an irreducible place component under the
operators commuting with the place actions span a nonzero subspace stable under everything), so
a `(𝔤, K)`-submodule embedding into it is a sum of copies of that component; a module of this
kind is irreducible as soon as some nonzero vector is mapped to a multiple of itself by every
`(𝔤, K)`-endomorphism. At a complex place such a vector is a lowest `U(n)`-type vector, and at a
real place a vector of the multiplicity-one `O(n)`-type.

This is a statement, not a proof.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic

/-- **Archimedean irreducibility from a multiplicity-one `O(n)`-type.** A multiplicity-one
`O(n)`-type in every real standard module (`Archimedean.RealStandardKTypeMultiplicityOne
Statement`) implies that the standard-module parameters of actual cuspidal realizations at
infinite places are irreducible (`CuspidalArchimedeanStandardIrreducibleStatement`). -/
def CuspidalArchimedeanStandardIrreducibleReductionStatement : Prop :=
  Archimedean.RealStandardKTypeMultiplicityOneStatement →
    CuspidalArchimedeanStandardIrreducibleStatement.{u}

end Langlands.Automorphic
