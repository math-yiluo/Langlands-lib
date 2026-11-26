import Langlands.BaseChange.TwistedCharacter.InducedRegularity
import Langlands.AllField.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.AllField.Representation.Parabolic.QuotientCompactProof

/-! # Regularity of evaluation on induced σ-traces of the general linear group -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory

universe u v uX

/-- The evaluation on a test satisfies the induced-family regularity condition
of twisted trace Paley–Wiener for a finite-order field automorphism. -/
def SigmaInducedTraceRegularityStatement : Prop :=
  ∀ (F : Type u) [CommRing F] [TopologicalSpace F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (d : ℕ), 0 < d → σ ^ d = 1 →
    ∀ (n : ℕ) [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
      [TotallyDisconnectedSpace (GeneralLinear n E)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
      (f : SchwartzBruhat (GeneralLinear n E)),
        IsSigmaInducedRegularFunctional.{u, v, uX} σ μ (Module.Dual.eval ℂ _ f)

/-- Apply compact-quotient trace regularity to the standard block parabolic. -/
theorem sigmaInducedTraceRegularity : SigmaInducedTraceRegularityStatement.{u, v, uX} := by
  intro F _ _ E _ _ _ _ _ _ σ d hd hσ n _ _ _ _ _ μ _ _ f B X _ _ Ξ hΞ _ BΞ
  have horder : (entrywiseAut σ n) ^ d = 1 := by
    let aut : (E ≃ₐ[F] E) →* MulAut (GeneralLinear n E) :=
      { toFun := fun s => entrywiseAut s n
        map_one' := MulEquiv.ext entrywiseAut_one_apply
        map_mul' := fun a b => MulEquiv.ext (entrywiseAut_mul_apply a b) }
    change aut σ ^ d = 1
    rw [← map_pow, hσ, map_one]
  let T := LocalFieldData.ofInstances E
  let : CompactSpace (Induction.LeftQuotient (B.parabolic E)) :=
    AllField.Parabolic.parabolicQuotientCompact E T B
  have hInfl : IsAdmissible (Ξ.comp (B.leviProjection E)) :=
    (AllField.Parabolic.leviInflationAdmissibility E T B X Ξ).mpr hΞ
  obtain ⟨c, hc⟩ := exists_inducedTwistedDistribution_twistCoefficients μ (entrywiseAut σ n)
    (continuous_entrywiseAut_of_isModuleTopology σ n)
    (TwistedPaleyWiener.continuous_entrywiseAut_symm σ n) hd horder
    (B.parabolic E) (B.isClosed_parabolic E) (entrywiseAut_mem_parabolic_iff σ B)
    (B.leviProjection E) (B.leviProjectionContinuous E).continuous
    (leviAut σ B) (leviProjection_entrywiseAut σ B) Ξ hInfl BΞ f
  refine ⟨c.support, c, fun ψ hψ hψθ hI => ?_⟩
  exact (hc ψ hψ hψθ hI).trans (by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul])

end Langlands.BaseChange
