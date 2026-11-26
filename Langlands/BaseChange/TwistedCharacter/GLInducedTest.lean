import Langlands.BaseChange.TwistedCharacter.InducedTest
import Langlands.BaseChange.TwistedCharacter.TwistRegularity
import Langlands.BaseChange.TwistedCharacter.CyclicExtension
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.AllField.Representation.Parabolic.QuotientCompactProof

/-! # Twisted trace transfer for the actual standard block Levi of general linear groups -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory

universe u v z

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E)
  {n : ℕ} (B : BlockShape n)

local notation "G" => GeneralLinear n E
local notation "M" => B.Levi E
local notation "κ" => LocalFieldData.leviHalfModulus (LocalFieldData.ofInstances E) B

private theorem halfModulus_invariant (m : M) : κ (leviAut σ B m) = κ m := by
  apply Units.ext
  rw [LocalFieldData.leviHalfModulus_apply, LocalFieldData.leviHalfModulus_apply,
    leviModulus_leviAut]

/-- The normalized section twist for an arbitrary standard-Levi intertwiner. -/
def normalizedParabolicSigmaIntertwiner
    {X : Type z} [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ M X)
    (A : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom)) :
    SigmaIntertwiner σ n ((LocalFieldData.ofInstances E).normalizedParabolicInduced B Ξ) :=
  TwistedPaleyWiener.inducedSigmaIntertwiner σ B (twist κ Ξ)
    (twistTwistedIntertwiner (leviAut σ B) κ (halfModulus_invariant σ B) A)

variable [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (B.Levi E)] [LocallyCompactSpace (B.Levi E)] [TotallyDisconnectedSpace (B.Levi E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (ν : Measure (B.Levi E)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

/-- The common test property in the actual unnormalized model. -/
theorem sigmaInducedTest {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) :
    TwistedInducedTestStatement.{v,v,z} μ ν (entrywiseAut σ n)
      (continuous_entrywiseAut_of_isModuleTopology σ n)
      (TwistedPaleyWiener.continuous_entrywiseAut_symm σ n)
      (B.parabolic E) (entrywiseAut_mem_parabolic_iff σ B) (B.leviProjection E)
      (leviAut σ B) (leviProjection_entrywiseAut σ B) := by
  let T := LocalFieldData.ofInstances E
  let : CompactSpace (Induction.LeftQuotient (B.parabolic E)) :=
    AllField.Parabolic.parabolicQuotientCompact E T B
  have horder : (entrywiseAut σ n) ^ d = 1 := by
    change (entrywiseAutHom n) σ ^ d = 1
    rw [← map_pow, hσ, map_one]
  exact twistedInducedTest.{v,v,z} μ ν (entrywiseAut σ n)
    (continuous_entrywiseAut_of_isModuleTopology σ n)
    (TwistedPaleyWiener.continuous_entrywiseAut_symm σ n) hd horder
    (B.parabolic E) (B.isClosed_parabolic E) (entrywiseAut_mem_parabolic_iff σ B)
    (B.leviProjection E) (B.leviProjectionContinuous E).continuous
    (isOpenMap_snd.comp (B.decompositionHomeomorph E).isOpenMap)
    (leviAut σ B) (leviProjection_entrywiseAut σ B)

/-- A linear transfer for normalized induction of actual twisted distributions of a Levi. -/
def SigmaNormalizedTraceTransferStatement : Prop :=
  ∃ T : Distribution M →ₗ[ℂ] Distribution G,
    ∀ (X : Type z) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ M X)
      (hΞ : IsAdmissible Ξ) (A : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
      (hI : IsAdmissible ((LocalFieldData.ofInstances E).normalizedParabolicInduced B Ξ)),
      T (twistedDistribution ν Ξ hΞ A.toLinearMap) =
        twistedDistribution μ _ hI (normalizedParabolicSigmaIntertwiner σ B Ξ A).toLinearMap

set_option maxHeartbeats 800000 in
/-- Multiplication of inducing tests by the half modulus implements normalized transfer. -/
theorem sigmaNormalizedTraceTransfer {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1) :
    SigmaNormalizedTraceTransferStatement.{u,v,z} σ B μ ν := by
  obtain ⟨T, hT⟩ := (sigmaInducedTest.{u,v,z} σ B μ ν hd hσ).exists_traceTransfer
  have hκ := (LocalFieldData.ofInstances E).isOpen_ker_leviHalfModulus B
  refine ⟨T.comp (characterTwistDistribution κ hκ), ?_⟩
  intro X _ _ Ξ hΞ A hI
  let A' := twistTwistedIntertwiner (leviAut σ B) κ (halfModulus_invariant σ B) A
  let hΞ' := (isAdmissible_twist_iff κ Ξ hκ).mpr hΞ
  have h := twistedDistribution_twist_eq_comp ν Ξ hΞ A.toLinearMap κ hκ hΞ'
  change T ((twistedDistribution ν Ξ hΞ A.toLinearMap).comp (characterMultiplyTest κ hκ)) = _
  rw [← h]
  exact hT X (twist κ Ξ) hΞ' A' hI

end Langlands.BaseChange
