import Langlands.Representation.Classification.RelativeCosocleHomComparisonProof
import Langlands.Representation.Classification.FineOppositeJacquetQuotientDetectionProof

/-! Actual fine-to-coarse quotient extraction for arbitrary tempered input. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW uZ

private theorem reflectionFineDataTransport
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} {C E : BlockShape n}
    (h : C = E) (ω : Rep.{uV} ℂ (C.Levi F.Carrier))
    (hi : Representation.IsIrreducible ω.ρ)
    (hc : letI := T.topology; CuspidalSupport.IsLeviCuspidal C ω.ρ) :
    letI := T.topology
    Representation.IsIrreducible (h ▸ ω).ρ ∧
      CuspidalSupport.IsLeviCuspidal E (h ▸ ω).ρ := by
  cases h
  exact ⟨hi, hc⟩

/-- A common actual irreducible outer quotient forces the actual untwisted
fine-to-coarse quotient, with no support premise on the tempered coarse input. -/
theorem glTemperedRelativeQuotientReflection :
    GLTemperedRelativeQuotientReflectionStatement.{uF,uV,uM,uW,uZ} := by
  intro p _ F T
  let := T.topology
  dsimp only
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀
    σ hσirr hσsq hqσ π hπirr hπtemp t ht J hJirr hqJ hqfine
  obtain ⟨hωBirr, hωBcusp⟩ :=
    reflectionFineDataTransport T h ω hωirr hωcusp
  obtain ⟨qJ, hqJ⟩ := hqJ
  have hJadm := ((relativeCosocleAdmissibility p F T n B π).2.2
    hπtemp.isAdmissible t).2.2 J qJ hqJ
  obtain ⟨houtfinite, hinfinite, heq⟩ :=
    relativeCosocleHomComparison.{uF,uV,uM,uW,uZ}
      p F T n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀
      σ hσirr hσsq hqσ π hπirr hπtemp t ht J hJirr ⟨qJ, hqJ⟩
  have hdetectt := fineOppositeJacquetQuotientDetection.{uF,uV,uW,uZ}
    Parabolic.normalizedSecondAdjointness.1 Parabolic.normalizedSecondAdjointness.2
      p F T n hn B S (h ▸ ω) hωBirr hωBcusp (h ▸ v₀) t
  obtain ⟨f, hf⟩ := (hdetectt.2 J hJadm hJirr).mpr hqfine
  let Hout := (fineTwist T B S (h ▸ ω) (h ▸ v₀) t).ρ.IntertwiningMap
    (T.normalizedComposedOppositeJacquet B S J.ρ)
  let Hin := (fineTwist T B S (h ▸ ω) (h ▸ v₀) 0).ρ.IntertwiningMap
    (T.normalizedRefinedOppositeJacquet B S π.ρ)
  let : FiniteDimensional ℂ Hout := houtfinite
  let : FiniteDimensional ℂ Hin := hinfinite
  have houtpos : 0 < Module.finrank ℂ Hout :=
    Module.finrank_pos_iff.mpr (nontrivial_iff.mpr ⟨f, 0, hf⟩)
  have hinpos : 0 < Module.finrank ℂ Hin := by
    rw [← heq]
    exact houtpos
  let : Nontrivial Hin := Module.finrank_pos_iff.mp hinpos
  obtain ⟨g, hg⟩ := exists_ne (0 : Hin)
  exact ((fineOppositeJacquetQuotientDetection.{uF,uV,uW,uZ}
    Parabolic.normalizedSecondAdjointness.1 Parabolic.normalizedSecondAdjointness.2
      p F T n hn B S (h ▸ ω) hωBirr hωBcusp (h ▸ v₀) 0).1
        π hπtemp.isAdmissible hπirr).mp ⟨g, hg⟩

end Langlands
