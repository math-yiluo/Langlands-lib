import Langlands.AlgebraicGeometry.Picard.MumfordProductGenericExtension
import Langlands.AlgebraicGeometry.Picard.ValuationRingTwoAxisExtensionStatement
import Langlands.CommutativeAlgebra.IntegralFibreProjectivityProof

/-! # Two-axis extension over arbitrary valuation rings -/

universe u

namespace Langlands.AbelianScheme

/-- A generic self-product line bundle trivial on both unit axes extends
over an arbitrary valuation domain, along the canonical product map. -/
theorem valuationRingTwoAxisExtension :
    ValuationRingTwoAxisExtensionStatement.{u} :=
  valuationRingTwoAxisExtension_of_integralFibreProjectivity.{u}
    Langlands.CommutativeAlgebra.integralFibreProjectivity.{u}

end Langlands.AbelianScheme
