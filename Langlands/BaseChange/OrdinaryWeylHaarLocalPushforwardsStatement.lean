import Langlands.BaseChange.OrdinaryWeylIntegralDecomposition
import Langlands.BaseChange.WeylDiscriminantTopology

/-! # Ordinary local Haar pushforwards for Weyl integration -/

namespace Langlands.BaseChange

open Langlands.QuotientIntegration MeasureTheory

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- Local pushforwards for the actual torus Haar measure and a compatible
quotient measure, with the absolute discriminant as density. -/
def OrdinaryWeylHaarLocalPushforwardsStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
    (T : WeylTorus F n) (μT : Measure T.val) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (ν : Measure (LeftQuotient T.val)), IsCompatible T.val μ μT ν →
    T.HasOrdinaryLocalPushforwards μ
      (T.weightedOrdinaryOrbitMeasure ν (μT.comap Subtype.val) T.discriminantWeight)

end Langlands.BaseChange
