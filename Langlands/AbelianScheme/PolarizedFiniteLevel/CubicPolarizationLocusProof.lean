import Langlands.AbelianScheme.PolarizedFiniteLevel.AlgebraicallyClosedFieldPolarizationDivisionProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.Assembly

/-! # The locally closed locus of cubic polarizations of prescribed degree -/

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The pullback of the embedding bundle is the cubic diagonal bundle of a
polarization of degree `d²`, up to a base twist, precisely on a locally closed
locus of the base. -/
theorem cubicPolarizationLocus : CubicPolarizationLocusStatement.{u} :=
  cubicPolarizationLocus_of_fieldDivision algebraicallyClosedFieldPolarizationDivision

end Langlands.AbelianScheme.PolarizedFiniteLevel
