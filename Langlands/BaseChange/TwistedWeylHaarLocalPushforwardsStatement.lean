import Langlands.BaseChange.TwistedWeylIntegralDecomposition
import Langlands.BaseChange.WeylDiscriminantTopology

/-! # Twisted local Haar pushforwards for Weyl integration -/

namespace Langlands.BaseChange

open Langlands.QuotientIntegration MeasureTheory

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- The regular norm domain and exact lifts with local pushforward identities
for the compatible quotient product weighted by the absolute discriminant. -/
def TwistedWeylHaarLocalPushforwardsStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type v) [CommRing E] [Algebra F E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
    (T : WeylTorus F n) (μT : Measure T.val) [μT.IsHaarMeasure],
    let H := T.val.map (baseChange F E n)
    ∀ (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
      (ν : Measure (LeftQuotient H)),
      Measure.map Subtype.val μH = Measure.map (fun t : T.val => baseChange F E n t.val) μT →
      IsCompatible H μ μH ν →
      MeasurableSet (T.regularNormPoints σ l) ∧
      ∃ (lift : T.regularNormPoints σ l → T.points E)
        (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val),
        T.HasTwistedLocalPushforwards hσ lift hlift μ
          (T.weightedTwistedOrbitMeasure σ l ν (μT.comap Subtype.val)
            (fun t => T.discriminantWeight ⟨t.val, t.property.1⟩))

end Langlands.BaseChange
