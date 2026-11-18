import Langlands.GroupScheme.Torus.NagataReductionStatements
import Langlands.GroupScheme.MatrixRepresentation.CanonicalComponentRegular
import Langlands.GroupScheme.Reductive.LinearlyReductiveFieldExtensionProof

/-! # The finite-component necessity in Nagata's theorem -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A linearly reductive affine algebraic group in nonzero characteristic has
geometric component order prime to the characteristic. -/
theorem nagataComponentOrderNecessity : NagataComponentOrderNecessityStatement.{u} := by
  intro k _ p _ _ G _ _ hG
  apply MatrixRepresentation.not_dvd_card_geometricComponents_of_baseChange_linearlyReductive G p
  exact (LinearReductivity.linearlyReductiveFieldExtension k (AlgebraicClosure k) G).mp hG

end Langlands.GroupScheme
