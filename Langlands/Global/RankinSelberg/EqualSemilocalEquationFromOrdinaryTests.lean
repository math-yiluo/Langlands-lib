import Langlands.Global.RankinSelberg.ArchimedeanCentralSignProof
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationOrdinaryReduction
import Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReduction
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProof
import Langlands.Global.RankinSelberg.RealLocalUniformPositiveEqualContinuationProof
import Langlands.Global.RankinSelberg.RealPlaceContragredientPairLProof

/-! # The equal-rank semi-local equation from ordinary archimedean tests -/

universe u uQ

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The equal-rank Rankin–Selberg functional equation for actual real-place restrictions. -/
theorem realEqualPlaceFunctionalEquation : RealEqualFunctionalEquationStatement.{u} := by
  apply realEqualFunctionalEquation_of_positiveJacquet
  intro F _ _ _ ψ hψ r hr T Td T' Td' hTd hTd' v a ha
    ds es dds ees hds hes hdds hees D W W' Φ hW hW'
  have hWm := (realPlaceUniformWhittakerModel F ψ hψ r T v a ha ds hds W).1 hW
  have hWm' := (realPlaceUniformWhittakerModel F ψ hψ r T' v a ha es hes W').2 hW'
  have hEq := realLocalUniformPositiveEqualJacquet_of_continuation
    realLocalUniformPositiveEqualContinuation r hr ds es hds.1 hes.1 a D W W' Φ hWm hWm'
  have hDen := realPlaceContragredientPairL F r r T Td T' Td' hTd hTd' v ds es dds ees
    hds hes hdds hees
  have hSign := RealLocalJacquet.realMinusOneScalar_eq_parameter T v ds hds
  simpa only [RealJacquet.EqualEquation, ← hDen, ← hSign] using hEq

/-- Ordinary equal-rank nonvanishing at the real and complex places in ranks above one
gives the equal-rank semi-local equation over every number field. -/
def EqualSemilocalEquationFromOrdinaryTestsStatement : Prop :=
  RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u} →
    ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u} →
    EqualSemilocalEquationStatement.{u, uQ}

theorem equalSemilocalEquationFromOrdinaryTests :
    EqualSemilocalEquationFromOrdinaryTestsStatement.{u, uQ} := by
  intro hReal hComplex
  have hFactorization := equalWhittakerPositiveRankReduction
    (infiniteWhittakerSliceModelPositiveRank_of_all infiniteWhittakerSliceModel)
    (realEqualPlaceTestsPositiveRank_of_ordinary realEqualPlaceFunctionalEquation hReal)
    (complexEqualPlaceTestsPositiveRank_of_ordinary hComplex)
  exact equalSemilocalReduction (equalSemilocalFactorizationReduction
    complexPlaceFunctionalEquation.2 realEqualPlaceFunctionalEquation hFactorization
    archimedeanCentralSign)

end Langlands.Global.RankinSelbergGlobal
