import Langlands.Representation.RankinSelberg.CompactDataStatement
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.HarmonicAnalysis.RowTestSmoothProof

/-! Simultaneous compact families of coefficient-model and row-test translates. -/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV uW

/-- Smooth coefficient models and a Schwartz–Bruhat row test have a simultaneous
locally constant translate family, finite on each compact subset. -/
theorem equalRankCompactData (F : Type uF) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] (n : ℕ) :
    EqualRankCompactDataStatement.{uF, uV, uW} F n := by
  intro V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f' Φ
  have hf : IsLocallyConstant (fun g => modelRepresentation π ℓ g f) :=
    Hecke.orbitMap_locallyConstant _ (model_isSmooth π hπ ℓ f)
  have hf' : IsLocallyConstant (fun g => modelRepresentation σ ℓ' g f') :=
    Hecke.orbitMap_locallyConstant _ (model_isSmooth σ hσ ℓ' f')
  have hD := hf.prodMk (hf'.prodMk (rowTranslate_locallyConstant Φ))
  refine ⟨hD, ?_⟩
  intro K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (hD.comp_continuous continuous_subtype_val).range_finite

end Langlands.RankinSelberg
