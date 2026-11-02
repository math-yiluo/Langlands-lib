import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotientReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.MonomorphismLocallyFiniteTypeSchemeProof
import Langlands.AlgebraicGeometry.SmoothEquivalenceRelationEtaleSliceProof
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientProof

/-! # The canonical etale quotient of a smooth relation on an algebraic space

A proof of `SmoothRelationQuotientStatement`: the reduction
`SmoothRelationQuotient.smoothRelationQuotientStatement_of` applied to the proofs of its four
prerequisite statements.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic-space equivalence relation with smooth projections on a scheme locally of
finite type over `S`, the canonical quotient is an fppf sheaf with representable diagonal and a
locally finite type etale atlas, the relation is the kernel pair of the quotient map, and the
quotient map is smooth and surjective. -/
theorem smoothRelationQuotient : SmoothRelationQuotientStatement.{u} :=
  SmoothRelationQuotient.smoothRelationQuotientStatement_of
    monomorphismLocallyFiniteTypeScheme
    smoothEquivalenceRelationEtaleSlice
    smoothEtaleSourceDescent
    etaleEquivalenceRelationAlgebraicSpaceQuotient

end Langlands.AlgebraicGeometry.AlgebraicSpace
