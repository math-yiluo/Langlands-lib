import Langlands.Geometry.Building.Kottwitz.TorusNormNaturality
import Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapProof
import Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof
import Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof
import Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonProof
import Langlands.Geometry.Building.Kottwitz.TorusMapProof

/-! # Assembly of the cocenter construction of the Kottwitz homomorphism -/

universe u

open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- The cocenter construction gives the unique surjective Kottwitz homomorphism
for every connected reductive group with simply connected derived group. -/
theorem simplyConnectedDerivedKottwitz_proof : SimplyConnectedDerivedKottwitzStatement.{u} :=
  simplyConnectedDerivedKottwitz_of_norm_inputs
    algebraicFundamentalGroupComparison algebraicFundamentalGroupMap
    torusFundamentalComparison_proof fundamentalInertiaMapStatement torusInertiaComparison_proof
    torusKottwitzExistence

end Langlands.Geometry.Building.Kottwitz
