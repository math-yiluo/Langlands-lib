import Langlands.GroupScheme.OddOrthogonalMatrix.BaseChange
import Langlands.GroupScheme.OddOrthogonalMatrix.PseudoReductive
import Langlands.GroupScheme.IdentityComponent.Transport

/-! # Geometric reductivity of the actual odd identity component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable (l : Type) [Fintype l] [DecidableEq l] (K : Type u) [Field K]

set_option linter.defProp false in
/-- The actual identity component of the split odd norm-one group is
connected reductive over every field, with at least two hyperbolic indices. -/
def identityReductive [Nontrivial l] : IsConnectedReductive (identityComponent (groupScheme l K)) where
  smooth := inferInstance
  isAffineHom := inferInstance
  connectedSpace := inferInstance
  hasTrivialGeometricUnipotentRadical :=
    HasTrivialUnipotentRadical.of_iso
      (IdentityComponent.baseChangeIso (groupScheme l K) (algebraMap K (AlgebraicClosure K)))
      (HasTrivialUnipotentRadical.of_iso
        (IdentityComponent.mapIso (baseChangeModelIso (l := l) (toAlgebraicClosure K)))
        (hasTrivialUnipotentRadical_identityComponent (l := l) (AlgebraicClosure K)))

end Langlands.GroupScheme.OddOrthogonalMatrix
