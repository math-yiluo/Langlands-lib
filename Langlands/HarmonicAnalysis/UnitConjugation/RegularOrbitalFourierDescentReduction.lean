import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierDescentStatement
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicIwasawaStatement
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicOrbitalIntegral
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicAveragedDensity
import Langlands.HarmonicAnalysis.UnitConjugation.PairingUnitHaar
import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.BaseChange.FiniteAlgebraAnalyticNorm
import Langlands.Galois.Local.AbsoluteDefinitions

/-! # Parabolic descent for Fourier transforms from compact Iwasawa factorization -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open UnitConjugation UnitConjugation.IdempotentCentralizer QuotientIntegration
open MeasureTheory Set _root_.Topology

universe u v

/-- Compact Iwasawa factorization for idempotent parabolics supplies the structural
input for descent of regular orbital Fourier local integrability. -/
def RegularOrbitalFourierDescentReduction.{u', v'} : Prop :=
  IdempotentParabolicIwasawaStatement.{u', v'} → RegularOrbitalFourierDescentStatement.{u', v'}

theorem regularOrbitalFourierDescentReduction : RegularOrbitalFourierDescentReduction.{u, v} := by
  intro hIwasawa F _ _ _ _ _ A _ _ _ _ e he X hX hLevi
    _ _ _ _ _ _ ψ B hB μ _ _ μG _ μH _ _ νG hG hconv
  let M : Subalgebra F A := Subalgebra.centralizer F ({e} : Set A)
  have : IsModuleTopology F M := isModuleTopology_submodule M.toSubmodule
  have : CompactOpenExhaustion A := compactOpenExhaustion_of_finiteDimensional F A
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : NormedRing A := BaseChange.finiteAlgebraNormedRing F A
  let : NormedAlgebra F A := BaseChange.finiteAlgebraNormedAlgebra F A
  have : IsUltrametricDist A := BaseChange.finiteAlgebraNormedRing_ultrametric F A
  have : ProperSpace A := FiniteDimensional.proper F A
  have : ProperSpace M := FiniteDimensional.proper F M
  have : ProperSpace (offDiagonalCorner F e) := FiniteDimensional.proper F _
  have hvalA := BaseChange.finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := A)
  have hvalM := BaseChange.finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := M)
  have : SecondCountableTopology Aˣ := hvalA.isEmbedding.secondCountableTopology
  have : SecondCountableTopology Mˣ := hvalM.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace Mˣ := hvalM.locallyCompactSpace
  let : MeasurableSpace Mˣ := borel _
  have : BorelSpace Mˣ := ⟨rfl⟩
  let J := conjugationCentralizer X
  let : MeasurableSpace (LeftQuotient J) := borel _
  have : BorelSpace (LeftQuotient J) := ⟨rfl⟩
  have hJ : IsClosed (J : Set Mˣ) := by
    have hEq : (J : Set Mˣ) = {g : Mˣ | (g : M) * X = X * (g : M)} :=
      Set.ext (mem_conjugationCentralizer_iff X)
    rw [hEq]
    exact isClosed_eq (Units.continuous_val.mul_const X) (continuous_const.mul Units.continuous_val)
  have : LocallyCompactSpace J := hJ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology J :=
    (IsEmbedding.subtypeVal (p := fun g : Mˣ => g ∈ J)).secondCountableTopology
  have : LocallyCompactSpace (LeftQuotient J) := leftQuotient_locallyCompactSpace J
  have : SecondCountableTopology (LeftQuotient J) :=
    (leftQuotient_isOpenQuotientMap J).secondCountableTopology
  have : T2Space (LeftQuotient J) := leftQuotient_t2Space J hJ
  let μMG : Measure Mˣ := Measure.haar
  have : μMG.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure Mˣ).IsHaarMeasure
  have hBM := invariantPairing_centralizer he hB
  have : μMG.IsMulRightInvariant := pairingUnitHaarUnimodularity F M _ μMG hBM
  have : μG.IsMulRightInvariant := pairingUnitHaarUnimodularity F A B μG hB
  let E := conjugationCentralizerEquiv he X hX
  let μJ := μH.map E.symm
  have : μJ.IsHaarMeasure := E.symm.isHaarMeasure_map μH
  have : μJ.IsMulRightInvariant := isMulRightInvariant_map E.symm μH
  have hE : MeasurePreserving E μJ μH := by
    have hEm : Measurable (E : J → conjugationCentralizer (X : A)) := E.continuous.measurable
    have hEs : Measurable (E.symm : conjugationCentralizer (X : A) → J) :=
      E.symm.continuous.measurable
    refine ⟨hEm, ?_⟩
    change (μH.map E.symm).map E = μH
    rw [Measure.map_map hEm hEs,
      show (E : J → conjugationCentralizer (X : A)) ∘ E.symm = id from
        funext E.apply_symm_apply, Measure.map_id]
  obtain ⟨νM, hM⟩ := compatibleMeasureExists J hJ μMG μJ
  have : νM.Regular := hM.regular
  obtain ⟨K, hK, hfac⟩ := hIwasawa F A e he
  let μK := μG.comap (K.toSubgroup.subtype : K →* Aˣ)
  have : μK.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) (f := K.toSubgroup.subtype) μG
      K.isOpen.isOpenEmbedding_subtypeVal
  obtain ⟨ν, c, hν, hc₀, hcTop, hOrbital⟩ :=
    map_parabolicOrbitalPoint F he X hX K hK hfac μG μMG μH μJ hE νG νM hG hM
  have : ν.IsAddHaarMeasure := hν
  obtain ⟨μM, hFourier⟩ := idempotentParabolicAveragedFourier e he ψ hB μ
    (K : Set Aˣ) hK μK ν
  obtain ⟨hconvM, hTerm⟩ :=
    idempotentParabolicOrbitalIntegral F X K he hK νG νM ν μK c hcTop hOrbital hconv
  obtain ⟨θ, hθ, hLeviDensity⟩ := hLevi ψ _ hBM μM μMG μJ νM hM hconvM
  obtain ⟨r, hr, hDensity⟩ := idempotentParabolicAveragedDensity F he K hK hvalA
    μG μ μM ν θ hθ
  have hc : c.toReal ≠ 0 := (ENNReal.toReal_pos hc₀ hcTop).ne'
  refine ⟨c.toReal⁻¹ • r, hr.smul _, fun f => ?_⟩
  let fP := parabolicConstantTerm F he ν (compactConjugationAverage (K : Set Aˣ) hK μK f)
  let fHat := pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f
  have hScaled :
      c.toReal • distributionFourier ψ hB.isSymm hB.nondegenerate μ
        (orbitalDistribution (X : A) νG hconv) f = ∫ x, r x * f x ∂μ.measure := by
    rw [distributionFourier_apply]
    change c.toReal • orbitalDistribution (X : A) νG hconv fHat = _
    rw [← hTerm fHat]
    change orbitalDistribution X νM hconvM (parabolicConstantTerm F he ν
      (compactConjugationAverage (K : Set Aˣ) hK μK
        (pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f))) = _
    rw [hFourier f]
    change distributionFourier ψ hBM.isSymm hBM.nondegenerate μM
      (orbitalDistribution X νM hconvM) fP = _
    exact (hLeviDensity fP).trans (hDensity f).symm
  calc
    _ = c.toReal⁻¹ • (c.toReal • distributionFourier ψ hB.isSymm hB.nondegenerate μ
        (orbitalDistribution (X : A) νG hconv) f) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c.toReal⁻¹ • ∫ x, r x * f x ∂μ.measure := congrArg (c.toReal⁻¹ • ·) hScaled
    _ = _ := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (smul_mul_assoc c.toReal⁻¹ (r x) (f x)).symm

end Langlands.HarmonicAnalysis
