import Langlands.CommutativeAlgebra.ResidueFieldFiniteProjectiveDimensionRegularStatement
import Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionLowerBoundProof
import Langlands.CommutativeAlgebra.ResidueFieldProjectiveDimensionUpperBoundProof

/-! # Assembly of the residue-field criterion from its two numerical bounds -/

universe u

namespace Langlands.CommutativeAlgebra

/-- A Noetherian local ring whose residue field has finite projective dimension is regular. -/
theorem residueFieldFiniteProjectiveDimensionRegular :
    ResidueFieldFiniteProjectiveDimensionRegularStatement.{u} := by
  intro R _ _ _ h
  exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R
    ((residueFieldProjectiveDimensionLowerBound R).trans
      (residueFieldProjectiveDimensionUpperBound R h))

end Langlands.CommutativeAlgebra
