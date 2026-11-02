import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedAddCommGroupSheafSchemeRepresentabilityReduction
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof

/-! # Scheme representability of separated commutative group spaces over a field

A proof of `SeparatedAddCommGroupSheafSchemeRepresentabilityStatement`: the reduction
`separatedAddCommGroupSheafSchemeRepresentability_of` applied to the proof of Stacks 03BM.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A separated fppf sheaf of commutative groups over a field with an etale surjective atlas
locally of finite type is represented by a separated scheme locally of finite type. -/
theorem separatedAddCommGroupSheafSchemeRepresentability :
    SeparatedAddCommGroupSheafSchemeRepresentabilityStatement.{u} :=
  separatedAddCommGroupSheafSchemeRepresentability_of
    finiteLocallyFreeEquivalenceRelationAffineQuotient

end Langlands.AlgebraicGeometry.AlgebraicSpace
