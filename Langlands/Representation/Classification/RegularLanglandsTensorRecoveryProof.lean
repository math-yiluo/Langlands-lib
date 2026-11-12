import Langlands.Representation.Classification.RegularLanglandsTensorRecoveryStatement
import Langlands.Representation.Classification.RegularLanglandsHeadAdapters
import Langlands.Representation.Classification.BlockTensorTemperedProof
import Langlands.Representation.Classification.RelativeCosocleHomComparisonProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Tensor.FiniteProperties

/-! Fixed-parameter recovery from the leading real block of an actual quotient. -/

noncomputable section

namespace Langlands

open CategoryTheory GeneralLinear RelativeRegularComparison CuspidalJacquetMultiplicity

universe uF uV uW uJ

set_option maxHeartbeats 1000000

/-- At one regular parameter, a common irreducible quotient recovers the
untwisted irreducible tempered whole-Levi representation. -/
theorem fixedRegularLeviRecovery
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (τ : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hσ : Representation.IsIrreducible σ.ρ) (hσt : IsLeviTempered T B σ)
    (hτ : Representation.IsIrreducible τ.ρ) (hτt : IsLeviTempered T B τ)
    (t : Fin B.length → ℝ) (ht : StrictAnti t)
    (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
    (hJ : Representation.IsIrreducible J.ρ)
    (qσ : (induced T B (Rep.of (T.leviRealPowerTwist B t σ.ρ))).ρ.IntertwiningMap J.ρ)
    (hqσ : Function.Surjective qσ)
    (qτ : (induced T B (Rep.of (T.leviRealPowerTwist B t τ.ρ))).ρ.IntertwiningMap J.ρ)
    (hqτ : Function.Surjective qτ) : Nonempty (σ.ρ.Equiv τ.ρ) := by
  let := T.topology
  let α := Rep.of (T.leviRealPowerTwist B t σ.ρ)
  let β := Rep.of (T.leviRealPowerTwist B t τ.ρ)
  let N := oppositeJacquet T B J
  obtain ⟨i, r, _, hfix⟩ :=
    Exponents.wholeInductionLeadingRealBlock p F T n hn B σ hσ hσt t ht
  obtain ⟨rQ, _, hQfix⟩ :=
    ActualQuotientRealBlock.quotientRetractionOfFiniteGeneration
      T hn B σ hσ hσt t
      (RelativeCosocleHomIsolationReduction.temperedInductionFiniteGeneration
        p F T n hn B σ hσ hσt t ht) J hJ qσ hqσ i r hfix
  have hadm := (relativeCosocleAdmissibility p F T n B τ).2.2 hτt.isAdmissible t
  let := hJ
  have hJnt : Nontrivial J.V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) J.ρ.asModule
  obtain ⟨g, hg⟩ := ActualQuotientRealBlock.nonzeroAdjunctionMap
    T hn B β J hJnt qτ hqτ hadm.1 (hadm.2.2 J qτ hqτ)
  have hgblock (v : β) : g v ∈ T.realCentralBlock B N.ρ
      (fun k => (B.size k : ℝ) * t k) := by
    apply map_mem_groupedCentralCharacterSpace g _
    change v ∈ T.realCentralBlock B β.ρ (fun k => (B.size k : ℝ) * t k)
    rw [TemperedCoarseRealBlock.realBlockEqTop T B τ hτt t]
    trivial
  let f : β.ρ.IntertwiningMap α.ρ := rQ.comp g
  have hf : f ≠ 0 := by
    intro hfzero
    apply hg
    ext v
    have h := hQfix (g v) (hgblock v)
    change ActualQuotientRealBlock.oppositeMap T B qσ (i (f v)) = g v at h
    rw [hfzero] at h
    change g v = 0
    change ActualQuotientRealBlock.oppositeMap T B qσ (i 0) = g v at h
    simpa only [map_zero] using h.symm
  let := (T.isIrreducible_leviRealPowerTwist_iff B t σ.ρ).mpr hσ
  let := (T.isIrreducible_leviRealPowerTwist_iff B t τ.ρ).mpr hτ
  let E : β.ρ.Equiv α.ρ :=
    f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)
  let f₀ : τ.ρ.IntertwiningMap σ.ρ :=
    untwistIntertwining (T.leviRealPowerCharacter B t) E.toIntertwiningMap
  exact ⟨(f₀.ofBijective E.bijective).symm⟩

private theorem tensorIrreducible
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : ∀ i, letI := T.topology
      Representation.IsIrreducible (σ i).representation)
    (htσ : ∀ i, letI := T.topology
      T.IsTempered (σ i).representation) :
    letI := T.topology
    Representation.IsIrreducible (B.blockTensor (fun i => (σ i).representation)) := by
  let := T.topology
  let := hσ
  exact FiniteTensor.isIrreducible_external (fun i => (σ i).representation)
    (fun i φ => (admissibleSchur_scalarEndomorphism _
      (htσ i).isAdmissible (hσ i) φ).exists)

/-- The exact fixed-shape, fixed-exponent recovery proposition. -/
theorem glRegularLanglandsTensorRecovery :
    GLRegularLanglandsTensorRecoveryStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn B σ τ hσ hτ htσ htτ t ht π κ hπ hκ hIso
  let d : T.TemperedLanglandsDatum.{max uF uV, uF} n := ⟨B, σ, hσ, htσ, t, ht⟩
  let e : T.TemperedLanglandsDatum.{max uF uV, uF} n := ⟨B, τ, hτ, htτ, t, ht⟩
  let A := Rep.of (B.blockTensor (fun i => (σ i).representation))
  let C := Rep.of (B.blockTensor (fun i => (τ i).representation))
  have hA : Representation.IsIrreducible A.ρ := tensorIrreducible T B σ hσ htσ
  have hC : Representation.IsIrreducible C.ρ := tensorIrreducible T B τ hτ htτ
  have hAt : IsLeviTempered T B A := by
    intro _ _ μ _
    exact (glBlockTensorTempered p F T n hn B (fun i => σ i)
      (fun i => (σ i).representation) hσ (fun i => (htσ i).isAdmissible)).mp htσ μ
  have hCt : IsLeviTempered T B C := by
    intro _ _ μ _
    exact (glBlockTensorTempered p F T n hn B (fun i => τ i)
      (fun i => (τ i).representation) hτ (fun i => (htτ i).isAdmissible)).mp htτ μ
  obtain ⟨hπirr, qd, hqd⟩ := hπ
  obtain ⟨_, qe, hqe⟩ := hκ
  obtain ⟨I⟩ := hIso
  let Ed := RegularHeadExistence.standardModuleLeviTwistEquiv T d
  let Ee := RegularHeadExistence.standardModuleLeviTwistEquiv T e
  let qA := qd.comp Ed.symm.toIntertwiningMap
  let qC := (SmoothRep.equivOfIso I).symm.toIntertwiningMap.comp
    (qe.comp Ee.symm.toIntertwiningMap)
  exact fixedRegularLeviRecovery T hn B A C hA hAt hC hCt t ht
    (Rep.of π.representation) hπirr qA (hqd.comp Ed.symm.surjective)
    qC ((SmoothRep.equivOfIso I).symm.surjective.comp (hqe.comp Ee.symm.surjective))

end Langlands
