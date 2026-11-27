import Langlands.Global.AdelicEisensteinRegularParameterProof
import Langlands.Global.AdelicIwasawaCompatibleMeasureProof
import Langlands.Global.AdelicRelativeWavePacketCompletenessComposition
import Langlands.Global.BoundedWavePacketReduction

/-! # Relative completeness from full completeness and the packet norm bound -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

/-- Lapid's norm bound supplies square integrability of the full packets. -/
theorem wavePacketSquareIntegrability_of_normBound (hNorm : BoundedWavePacketNormBoundStatement) :
    WavePacketSquareIntegrabilityStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho _ Θ hΘ
  obtain ⟨P, M, U, A, _, _, _, _, p, hp, iU, l, hUp, a, r, _, _, _, hA, hT, hU, hK, n, e, k,
    v, c, E, D, hv, hc, hD, hE, hReg, hEq⟩ := hΘ
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType (j := p) hp
  obtain ⟨-, -, π, -, -, hπ, -⟩ := r.isCompatible.levi.exists_unipotentRadical_retraction
  obtain ⟨μM, hμMHaar, hμM⟩ :=
    iwasawaCompatibleMeasureExistence F G P M U A p iU l a r hG hU K hK hKmax
  obtain ⟨β, hβc, hβs, hβ1⟩ := BoundedWavePacket.exists_weight n
  let S := ⋃ j, tsupport (c j)
  have hS : IsCompact S := isCompact_iUnion fun j => (hc j).2
  have hcS (j : Fin k) : ∀ x ∉ S, c j x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hxj => hx (mem_iUnion.mpr ⟨j, hxj⟩)
  have hSD : (fun x => imaginaryParameter F P (e x)) '' S ⊆ D := by
    rintro _ ⟨x, _, rfl⟩
    exact hD ⟨e x, rfl⟩
  obtain ⟨-, hMem, -⟩ := localWavePacketNormBound_of_bounded hNorm F G P M U A p iU l a r
    hA hT π hG hU hπ K hK rho hsmooth hcalc hKmax hrho μM hμM e β hβc hβs hβ1 k v c S E D
    hv hS (fun j => ⟨(hc j).1, hcS j⟩) hSD hE hReg
  simpa only [hEq, rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure] using hMem

/-- Full-quotient completeness and the packet norm bound imply relative-quotient completeness. -/
def RelativeWavePacketCompletenessFromNormBoundStatement : Prop :=
  WavePacketCompletenessStatement → BoundedWavePacketNormBoundStatement →
    RelativeWavePacketCompletenessStatement

/-- Use the packet norm bound to justify central averaging in the completeness transfer. -/
theorem relativeWavePacketCompleteness_of_normBound : RelativeWavePacketCompletenessFromNormBoundStatement :=
  fun hFull hNorm =>
    relativeWavePacketCompleteness_of_standard_of_squareIntegrable
      (standardWavePacketCompleteness_of_full hFull) (wavePacketSquareIntegrability_of_normBound hNorm)
      (eisensteinContinuationAmbientShift_of_regularParameter eisensteinRegularParameter)

end Langlands.Global
