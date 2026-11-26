import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.Group.GL.IntegralSubgroup
import Langlands.Group.GL.LocalFieldTopology

/-! # Statement: the twisted van Dijk formula for normalized product inductions

This module states the twisted van Dijk formula of Henniart–Lemaire (2011), II.4.5 (2), for
the normalized product induction of a σ-stable family of admissible block representations of
`GL_n(E)`. It supplies no proof. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear JacquetLanglands

universe u v uW

/-- Twisted van Dijk formula (Henniart–Lemaire 2011, II.4.5 (2)). Let `E` be a nonarchimedean
local field, `σ` an automorphism of `E` over a topological field `F` for which `E` has the
`F`-module topology, `B` a block shape of `n` and `P i` admissible representations of the
blocks with σ-intertwiners `A i`. Take Haar measures on `G = GL_n(E)`, on the Levi
`M = B.Levi E` and on the unipotent radical `U` giving volume one to `K = GL_n(𝒪_E)`,
`M(𝒪_E)` and `U(𝒪_E) = U ∩ K`, and the Haar probability measure on `K`. If a test function
`ψ` on `M` has the values
`ψ(m) = δ_P(m)^{1/2} ∫_U ∫_K φ(k⁻¹ m u σ(k)) dk du`, then the twisted distribution of the
normalized product induction at `φ`, for `ι(A)`, is the twisted distribution of the Levi
tensor representation at `ψ`, for `A₁ ⊗ ⋯ ⊗ A_r`. -/
def TwistedVanDijkStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (n : ℕ) (B : BlockShape n)
    (W : Fin B.length → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i))
    (hP : ∀ i, IsAdmissible (P i)) (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)),
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    letI : MeasurableSpace (B.Levi E) := borel _
    haveI : BorelSpace (B.Levi E) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space E n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
    haveI : ∀ i, T2Space (GeneralLinear (B.size i) E) := fun i =>
      LocalFieldTopology.generalLinear_t2Space E (B.size i)
    haveI : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) := fun i =>
      LocalFieldTopology.generalLinear_locallyCompactSpace E (B.size i)
    haveI : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E) := fun i =>
      LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (B.size i)
    ∀ (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
      (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
      (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
      (μK : Measure (GeneralLinearGroup.integralSubgroup (Fin n)
        (ValuativeRel.valuation E).integer)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK],
      μG (GeneralLinearGroup.integralSubgroup (Fin n) (ValuativeRel.valuation E).integer) = 1 →
      μM {x | ∀ i, x i ∈ GeneralLinearGroup.integralSubgroup (Fin (B.size i))
        (ValuativeRel.valuation E).integer} = 1 →
      μU {y | (y : GeneralLinear n E) ∈
        GeneralLinearGroup.integralSubgroup (Fin n) (ValuativeRel.valuation E).integer} = 1 →
      ∀ (φ : SchwartzBruhat (GeneralLinear n E)) (ψ : SchwartzBruhat (B.Levi E)),
        (∀ x : B.Levi E, ψ x = ((LocalFieldData.ofInstances E).leviHalfModulus B x : ℂ) *
          ∫ y, ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ * B.leviEmbedding E x *
            (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK ∂μU) →
        twistedDistribution μG ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
            (isAdmissible_normalizedProductInduced B P hP)
            (inducedSigmaIntertwiner σ B A).toLinearMap φ =
          twistedDistribution μM (B.blockTensor P) (FiniteTensor.isAdmissible_external P hP)
            (leviTensorIntertwiner σ B A).toLinearMap ψ

end Langlands.BaseChange
