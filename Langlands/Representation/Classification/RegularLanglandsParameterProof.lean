import Langlands.Representation.Classification.RegularLanglandsParameterStatement
import Langlands.Representation.Classification.RegularLanglandsHeadAdapters
import Langlands.Representation.Classification.BlockTensorTemperedProof
import Langlands.Representation.Classification.TemperedJointSupportProof
import Langlands.Representation.Exponents.SupportedRegularWeylConeComparisonProof
import Langlands.Representation.Exponents.SupportedRegularWeylParameterNumericsProof
import Langlands.Representation.Exponents.BlockParameterPermutationRigidityProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Tensor.FiniteProperties

/-! Ordered block ranks and real parameters of arbitrary regular Langlands quotients. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV

set_option maxHeartbeats 2000000

private theorem datumTensor_irreducible
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (d : T.TemperedLanglandsDatum.{uV, uF} n) :
    letI := T.topology
    Representation.IsIrreducible
      (d.shape.blockTensor (fun i => (d.blocks i).representation)) := by
  let := T.topology
  let := d.irreducible
  exact FiniteTensor.isIrreducible_external (fun i => (d.blocks i).representation)
    (fun i φ => (admissibleSchur_scalarEndomorphism _
      (d.tempered i).isAdmissible (d.irreducible i) φ).exists)

private theorem datumTensor_tempered
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (d : T.TemperedLanglandsDatum.{uV, uF} n) :
    letI := T.topology
    RelativeRegularComparison.IsLeviTempered T d.shape
      (Rep.of (d.shape.blockTensor (fun i => (d.blocks i).representation))) := by
  let := T.topology
  intro _ _ μ _
  exact (glBlockTensorTempered p F T n hn d.shape (fun i => d.blocks i)
    (fun i => (d.blocks i).representation) d.irreducible
    (fun i => (d.tempered i).isAdmissible)).mp d.tempered μ

/-- Isomorphic arbitrary irreducible quotients determine the ordered block
ranks and real determinant exponents of regular tempered Langlands data. -/
theorem glRegularLanglandsParameterUniqueness :
    GLRegularLanglandsParameterUniquenessStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn d e π τ hd he hπt
  obtain ⟨hπ, qd, hqd⟩ := hd
  obtain ⟨_, qe, hqe⟩ := he
  obtain ⟨E⟩ := hπt
  let πd := Rep.of (d.shape.blockTensor (fun i => (d.blocks i).representation))
  let πe := Rep.of (e.shape.blockTensor (fun i => (e.blocks i).representation))
  have hπd : Representation.IsIrreducible πd.ρ := datumTensor_irreducible T d
  have hπe : Representation.IsIrreducible πe.ρ := datumTensor_irreducible T e
  have hπdt : RelativeRegularComparison.IsLeviTempered T d.shape πd :=
    datumTensor_tempered T hn d
  have hπet : RelativeRegularComparison.IsLeviTempered T e.shape πe :=
    datumTensor_tempered T hn e
  let Ed := RegularHeadExistence.standardModuleLeviTwistEquiv T d
  let Ee := RegularHeadExistence.standardModuleLeviTwistEquiv T e
  have hqd' : ∃ q : (CuspidalJacquetMultiplicity.induced T d.shape
      (Rep.of (T.leviRealPowerTwist d.shape d.exponent πd.ρ))).ρ.IntertwiningMap
        π.representation, Function.Surjective q :=
    ⟨qd.comp Ed.symm.toIntertwiningMap, hqd.comp Ed.symm.surjective⟩
  have hqe' : ∃ q : (CuspidalJacquetMultiplicity.induced T e.shape
      (Rep.of (T.leviRealPowerTwist e.shape e.exponent πe.ρ))).ρ.IntertwiningMap
        π.representation, Function.Surjective q :=
    ⟨(SmoothRep.equivOfIso E).symm.toIntertwiningMap.comp
        (qe.comp Ee.symm.toIntertwiningMap),
      (SmoothRep.equivOfIso E).symm.surjective.comp
        (hqe.comp Ee.symm.surjective)⟩
  obtain ⟨Q1, R1, S1, h1, ω1, v1, σ1, hω1, hω1c, hω1u, hv1,
      hσ1, hσ1sq, qFM1, qMC1, qFC1, hqFM1, hqMC1, hqFC1⟩ :=
    glTemperedJointSupport p F T n hn d.shape πd hπd hπdt
  obtain ⟨Q2, R2, S2, h2, ω2, v2, σ2, hω2, hω2c, hω2u, hv2,
      hσ2, hσ2sq, qFM2, qMC2, qFC2, hqFM2, hqMC2, hqFC2⟩ :=
    glTemperedJointSupport p F T n hn e.shape πe hπe hπet
  obtain ⟨w, _, _, hrel, hcone1, hcone2⟩ :=
    glSupportedRegularWeylConeComparison p F T n hn
      d.shape Q1 R1 S1 h1 ω1 hω1 hω1c hω1u v1 hv1 σ1 hσ1 hσ1sq
      ⟨qFM1, hqFM1⟩ πd hπd hπdt ⟨qMC1, hqMC1⟩ ⟨qFC1, hqFC1⟩
      d.exponent d.strictAnti
      e.shape Q2 R2 S2 h2 ω2 hω2 hω2c hω2u v2 hv2 σ2 hσ2 hσ2sq
      ⟨qFM2, hqFM2⟩ πe hπe hπet ⟨qMC2, hqMC2⟩ ⟨qFC2, hqFC2⟩
      e.exponent e.strictAnti (Rep.of π.representation) hπ hqd' hqe'
  let V1 : Fin n → ℝ := fun a => (h1 ▸ v1) (blockIndex (d.shape.flatten S1) a)
  let V2 : Fin n → ℝ := fun a => (h2 ▸ v2) (blockIndex (e.shape.flatten S2) a)
  let A1 : Fin n → ℝ := fun a => d.exponent (blockIndex d.shape a)
  let A2 : Fin n → ℝ := fun a => e.exponent (blockIndex e.shape a)
  change ∀ a, V1 (w.symm a) - A1 (w.symm a) = V2 a - A2 a at hrel
  change Exponents.IsClosedPositiveRootCone (fun a => V1 (w.symm a)) at hcone1
  change Exponents.IsClosedPositiveRootCone (fun a => V2 (w a)) at hcone2
  obtain ⟨hV1cone, horth1, hanti1⟩ :=
    Exponents.supportedRegularWeylParameterNumerics.2.1
      n d.shape Q1 R1 S1 h1 v1 d.exponent hv1
  obtain ⟨_, horth2, hanti2⟩ :=
    Exponents.supportedRegularWeylParameterNumerics.2.1
      n e.shape Q2 R2 S2 h2 v2 e.exponent hv2
  have hrel' : ∀ a, V2 (w a) - A2 (w a) = V1 a - A1 a := by
    intro a
    simpa only [Equiv.symm_apply_apply] using (hrel (w a)).symm
  have hV := (Exponents.supportedRegularWeylParameterNumerics.2.2
    n V1 V2 A1 A2 w w.symm horth1 horth2
    (hanti1 d.strictAnti) (hanti2 e.strictAnti) hcone1 hcone2 hrel hrel' hV1cone).1
  apply Exponents.blockParameterPermutationRigidity n d.shape e.shape
    d.exponent e.exponent d.strictAnti e.strictAnti
  refine ⟨w, ?_⟩
  intro a
  have hr := hrel (w a)
  have hv := hV (w a)
  simp only [Equiv.symm_apply_apply] at hr hv
  change A1 a = A2 (w a)
  linarith only [hr, hv]

end Langlands
