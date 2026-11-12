import Langlands.Representation.Exponents.TemperedReflectionBranchObstructionStatement
import Langlands.Representation.Classification.RelativeCosocleHomComparisonProof
import Langlands.Representation.Classification.FineOppositeJacquetQuotientDetectionProof

/-!
# The selected tempered-reflection obstruction from independent Hom comparison

The no-inner-quotient hypothesis contradicts the published, independently
proved comparison of actual fine Hom spaces for the specified outer quotient.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uM uW uZ

private theorem branchTransportFineData
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} {C D : BlockShape n} (h : C = D)
    (ω : Rep.{uV} ℂ (C.Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → CuspidalSupport.IsLeviCuspidal C ω.ρ →
      Representation.IsIrreducible (h ▸ ω : Rep.{uV} ℂ (D.Levi F.Carrier)).ρ ∧
        CuspidalSupport.IsLeviCuspidal D (h ▸ ω : Rep.{uV} ℂ (D.Levi F.Carrier)).ρ := by
  cases h
  exact fun hi hc => ⟨hi, hc⟩

set_option maxHeartbeats 1000000 in
/-- The exact selected-branch obstruction. Independent actual-quotient Hom
comparison makes the sole extra no-inner-quotient hypothesis impossible. -/
theorem glTemperedReflectionBranchObstruction :
    GLTemperedReflectionBranchObstructionStatement.{uF, uV, uM, uW, uZ} := by
  dsimp only [GLTemperedReflectionBranchObstructionStatement]
  intro p _ F T
  let := T.topology
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀
    σ hσirr hσsq hqσ π hπirr hπtemp t ht J hJirr hqπJ hqfineJ hno
  exfalso
  let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
  let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
  obtain ⟨hωBirr, hωBcusp⟩ := branchTransportFineData T h ω hωirr hωcusp
  have hπadm : IsAdmissible π.ρ := hπtemp.isAdmissible
  obtain ⟨qπJ, hqπJsurj⟩ := hqπJ
  have hJadm : IsAdmissible J.ρ :=
    ((relativeCosocleAdmissibility.{uF, uW, uZ} p F T n B π).2.2 hπadm t).2.2
      J qπJ hqπJsurj
  have hdetect := fineOppositeJacquetQuotientDetection.{uF, uV, uW, uZ}
    Parabolic.normalizedSecondAdjointness.1 Parabolic.normalizedSecondAdjointness.2
      p F T n hn B S ωB hωBirr hωBcusp vB
  obtain ⟨f, hf⟩ := ((hdetect t).2 J hJadm hJirr).mpr hqfineJ
  have hcmp := relativeCosocleHomComparison.{uF, uV, uM, uW, uZ}
    p F T n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀
      σ hσirr hσsq hqσ π hπirr hπtemp t ht J hJirr ⟨qπJ, hqπJsurj⟩
  let Hout := (fineTwist T B S ωB vB t).ρ.IntertwiningMap
    (T.normalizedComposedOppositeJacquet B S J.ρ)
  let Hin := (fineTwist T B S ωB vB 0).ρ.IntertwiningMap
    (T.normalizedRefinedOppositeJacquet B S π.ρ)
  let : FiniteDimensional ℂ Hout := hcmp.1
  let : FiniteDimensional ℂ Hin := hcmp.2.1
  let : Nontrivial Hout := ⟨⟨f, 0, hf⟩⟩
  have hpos : 0 < Module.finrank ℂ Hin := by
    rw [← hcmp.2.2]
    exact Module.finrank_pos
  let : Nontrivial Hin := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨f₀, hf₀⟩ := exists_ne (0 : Hin)
  exact hno (((hdetect 0).1 π hπadm hπirr).mp ⟨f₀, hf₀⟩)

end Langlands
