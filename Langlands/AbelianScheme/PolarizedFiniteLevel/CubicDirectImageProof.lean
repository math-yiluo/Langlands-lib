import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageReductionProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyProof

/-! # Proof of the cubic direct-image theorem -/

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The direct image of the cubic diagonal bundle of a datum with `0 < d` is locally free of
rank `6^g*d`, and its canonical base-change map along every morphism is an isomorphism. -/
theorem cubicDirectImage : CubicDirectImageStatement.{u} :=
  cubicDirectImageReduction cubicFibreCohomology

end Langlands.AbelianScheme.PolarizedFiniteLevel
