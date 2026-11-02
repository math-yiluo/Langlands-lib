import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectrumStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.PointAmalgamationProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteJointImage
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # Spectrum embedding for every full presented affinoid domain -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

/-- The stored structural spectrum map of every full domain representation
is a closed embedding. -/
theorem spectrumEmbedding : SpectrumEmbeddingStatement.{u} := by
  intro K _ _ _ A U
  apply U.spectrumMap.continuous.isClosedEmbedding
  intro x y hxy
  obtain ⟨L, instField, instUltra, instComplete, instAlg, f, g, hcomm, hf, hg⟩ :=
    pointAmalgamation K A U.algebra U.algebra U.baseMap U.baseMap x y hxy
  let := instField
  let := instUltra
  let := instComplete
  let := instAlg
  let D := finiteJointImage f g
  have hcomp : D.left.comp U.baseMap = D.right.comp U.baseMap :=
    D.comp_eq U.baseMap U.baseMap hcomm
  have hφ : HasImageIn K (D.left.comp U.baseMap) U.locus := by
    intro z
    have hpoint : BanachSpectrum.comap (D.left.comp U.baseMap).toBoundedRingHom z =
        BanachSpectrum.comap U.baseMap.toBoundedRingHom
          (BanachSpectrum.comap D.left.toBoundedRingHom z) :=
      BanachSpectrum.ext fun _ => rfl
    rw [hpoint]
    exact U.represents.hasImageIn _
  have hmaps : D.left = D.right :=
    (U.represents.2.2 D.algebra (D.left.comp U.baseMap) hφ).unique rfl hcomp.symm
  have hfg : f = g := by
    calc
      f = D.embed.comp D.left := D.embed_left.symm
      _ = D.embed.comp D.right := congrArg (fun η => D.embed.comp η) hmaps
      _ = g := D.embed_right
  apply BanachSpectrum.ext
  intro b
  rw [← hf b, ← hg b, hfg]

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
