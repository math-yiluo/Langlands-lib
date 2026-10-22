import Langlands.Geometry.Analytic.Spectrum.Statement
import Langlands.Geometry.Analytic.Spectrum.LaurentNeighborhoods

/-! # Proof of the complete multiplicative spectrum foundation target -/

universe u v w

namespace Langlands.Analytic

theorem spectrumProperties : SpectrumPropertiesStatement.{u, v, w} := by
  refine ⟨?_, ?_, ?_⟩
  · intro A _
    refine ⟨⟨BanachSpectrum.evaluation_isEmbedding,
      BanachSpectrum.isClosed_range_evaluation⟩, inferInstance, inferInstance,
      BanachSpectrum.kernel_isPrime, ?_, ?_,
      BanachSpectrum.exists_compact_finite_laurent_neighborhood⟩
    · intro K _ _ x c
      exact BanachSpectrum.algebraMap_apply x c
    · intro ι κ f r g s
      exact ⟨BanachSpectrum.isClosed_laurentLocus f r g s,
        BanachSpectrum.isCompact_laurentLocus f r g s⟩
  · intro K _ x a
    exact BanachSpectrum.field_apply x a
  · intro A _ B _ φ ι κ f r g s
    exact BanachSpectrum.preimage_laurentLocus φ f r g s

end Langlands.Analytic
