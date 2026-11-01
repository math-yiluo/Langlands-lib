import Langlands.Representation.RankinSelberg.CorankOneEntireSliceStatement
import Langlands.Representation.RankinSelberg.CorankCommonCompactSupport
import Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation

/-!
# Entire dependence on corank determinant slices

The common right level first gives a common compact quotient support on each
fixed determinant slice. Smoothness of the fixed coefficient then gives a finite
orbit formula for the actual restricted integrals, independent of the parameter.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-- Every corank determinant slice of a common-level pointwise entire family is
integrable and has an entire literal slice coefficient. -/
theorem corankOneEntireSlice : CorankOneEntireSliceStatement.{uF,uV} := by
  intro p _ F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ r
  let := borel (Langlands.GeneralLinear (r + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (r + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient r F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
  intro _ ν hν V _ _ τ hτ ℓ Wprime U hK hU m
  obtain ⟨K, hKo, _, hKinv⟩ := hK
  obtain ⟨C, hC, hCs⟩ := CommonLevel.corank_common_compact_support
    F.canonicalTopologicalData r ψ U K hKo hKinv m
  have := hν.regular
  exact CommonLevel.corank_slice_of_common_support F.canonicalTopologicalData r
    ψ ν V τ hτ ℓ Wprime U K hKo hKinv hU m C hC (fun z => hCs z _ 0)

end Langlands.RankinSelberg
