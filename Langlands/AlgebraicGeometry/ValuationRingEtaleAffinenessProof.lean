import Langlands.AlgebraicGeometry.ValuationRingEtaleAffinenessStatement
import Langlands.AlgebraicGeometry.ValuationFpqcAffineModel

/-! # Affineness of quasi-compact separated etale valuation schemes -/

universe u

namespace Langlands.AlgebraicGeometry

/-- Every quasi-compact separated etale scheme over an arbitrary valuation
domain is affine. -/
theorem valuationRingEtaleAffineness : ValuationRingEtaleAffinenessStatement.{u} := by
  intro R _ _ _ X f hqc hsep het
  let : _root_.AlgebraicGeometry.QuasiCompact f := hqc
  let : _root_.AlgebraicGeometry.IsSeparated f := hsep
  let : _root_.AlgebraicGeometry.Etale f := het
  exact isAffineHom_etale_over_valuationDomain (CommRingCat.of R) f

end Langlands.AlgebraicGeometry
