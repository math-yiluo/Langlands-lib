import Langlands.BaseChange.TwistedInducedCharacterFormulaStatement
import Langlands.BaseChange.TwistedVanDijkStatement
import Langlands.BaseChange.TwistedLocalDescentStatement
import Langlands.BaseChange.RelativeParabolicDiscriminantNorm
import Langlands.AllField.LocalField.Foundation

/-! # The twisted induced character formula from van Dijk's formula and local descent

`twistedInducedCharacterFormulaReduction` proves that the twisted van Dijk formula
(`TwistedVanDijkStatement`) and the local descent of the twisted constant term
(`TwistedLocalDescentStatement`) imply `TwistedInducedCharacterFormulaStatement`
(Henniart–Lemaire 2011, II.4.5 (3)). The module also proves that twisted local values do not
depend on the Haar measure. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear JacquetLanglands

section Measures

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- A compact set with nonempty interior has mass one for some Haar measure. -/
theorem exists_isHaarMeasure_eq_one {C : Set G} (hC : IsCompact C) (hC' : (interior C).Nonempty) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ μ C = 1 :=
  ⟨Measure.haarMeasure ⟨⟨C, hC⟩, hC'⟩, inferInstance, Measure.haarMeasure_self⟩

/-- A compact group has a Haar probability measure. -/
theorem exists_isHaarMeasure_isProbabilityMeasure [CompactSpace G] :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ IsProbabilityMeasure μ := by
  obtain ⟨μ, hμ, h1⟩ := exists_isHaarMeasure_eq_one (G := G) isCompact_univ
    (by rw [interior_univ]; exact Set.univ_nonempty)
  exact ⟨μ, hμ, ⟨h1⟩⟩

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Twisted local values do not depend on a positive rescaling of the measure. -/
theorem hasLocalValue_twistedDistribution_of_eq_smul (μ₀ μ : Measure G)
    [IsFiniteMeasureOnCompacts μ₀] [μ₀.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (r : NNReal) (hμ : μ = r • μ₀) (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (A : Module.End ℂ V) {g : G} {c : ℂ}
    (h : HasLocalValue μ₀ (twistedDistribution μ₀ ρ hρ A) g c) :
    HasLocalValue μ (twistedDistribution μ ρ hρ A) g c := by
  obtain ⟨U, hU, hg, hf⟩ := h
  refine ⟨U, hU, hg, fun f hsupp => ?_⟩
  have hact : Hecke.integratedAction μ ρ hρ.1 f =
      (r : ℂ) • Hecke.integratedAction μ₀ ρ hρ.1 f := by
    ext v
    simp only [Hecke.integratedAction_apply, LinearMap.smul_apply]
    rw [hμ]
    simp only [AlgebraicIntegral.integral, Measure.smul_apply, Finset.smul_sum, smul_smul,
      ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, Complex.ofReal_mul]
  have hΘ : twistedDistribution μ ρ hρ A f = (r : ℂ) * twistedDistribution μ₀ ρ hρ A f := by
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← twistedDistribution_smul,
      twistedDistribution_apply, twistedDistribution_apply]
    apply congrArg FiniteRankEnd.trace
    apply Subtype.ext
    change (Hecke.integratedAction μ ρ hρ.1 f).comp A =
      (Hecke.integratedAction μ₀ ρ hρ.1 f).comp ((r : ℂ) • A)
    rw [hact, LinearMap.smul_comp, LinearMap.comp_smul]
  have hint : (∫ y, f y ∂μ) = (r : ℂ) * ∫ y, f y ∂μ₀ := by
    rw [hμ, integral_smul_nnreal_measure]
    rfl
  rw [hΘ, hf f hsupp, hint]
  ring

end Measures

section Values

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- In a second countable group, a twisted local value for one Haar measure is a twisted
character value. -/
theorem hasTwistedCharacterValue_of_hasLocalValue
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (A : Module.End ℂ V) {g : G} {c : ℂ}
    (h : letI : MeasurableSpace G := borel G
      haveI : BorelSpace G := ⟨rfl⟩
      ∃ (μ₀ : Measure G) (_ : μ₀.IsHaarMeasure),
        HasLocalValue μ₀ (twistedDistribution μ₀ ρ hρ A) g c) :
    HasTwistedCharacterValue ρ hρ A g c := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ₀, _, h⟩ := h
  intro μ _
  exact hasLocalValue_twistedDistribution_of_eq_smul μ₀ μ _
    (Measure.isMulLeftInvariant_eq_smul μ μ₀) ρ hρ A h

end Values

section Reduction

universe u v uW

/-- The tensor product of block σ-intertwiners intertwines the Levi tensor representation with
its pullback along `leviAut σ B`, in the form used for twisted conjugation. -/
theorem leviTensorIntertwiner_comp {F : Type u} [CommRing F] {E : Type v} [CommRing E]
    [Algebra F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}
    (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) (g : B.Levi E) :
    (leviTensorIntertwiner σ B A).toLinearMap ∘ₗ B.blockTensor P g =
      B.blockTensor P ((leviAut σ B).toMonoidHom g) ∘ₗ
        (leviTensorIntertwiner σ B A).toLinearMap :=
  (leviTensorIntertwiner σ B A).isIntertwining' g

/-- The twisted van Dijk formula and the local descent of the twisted constant term together
imply the twisted induced character formula of Henniart–Lemaire (2011), II.4.5 (3). -/
def TwistedInducedCharacterFormulaReductionStatement : Prop :=
  TwistedVanDijkStatement.{u, v, uW} → TwistedLocalDescentStatement.{u, v} →
    TwistedInducedCharacterFormulaStatement.{u, v, uW}

/-- `TwistedInducedCharacterFormulaStatement` follows from the twisted van Dijk formula and the
local descent of the twisted constant term. -/
theorem twistedInducedCharacterFormulaReduction :
    TwistedInducedCharacterFormulaReductionStatement.{u, v, uW} := by
  intro hVD hLD F _ _ _ _ E _ _ _ _ _ _ σ l n hE hn B W _ _ P hP A _ δ γ hδγ hγ k m hm d hd b hb
  have : ∀ i, T2Space (GeneralLinear (B.size i) E) := fun i =>
    LocalFieldTopology.generalLinear_t2Space E (B.size i)
  have : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) := fun i =>
    LocalFieldTopology.generalLinear_locallyCompactSpace E (B.size i)
  have : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E) := fun i =>
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (B.size i)
  have := LocalFieldTopology.generalLinear_t2Space E n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
  have := LocalFieldTopology.generalLinear_secondCountableTopology E n
  let _ : MeasurableSpace (GeneralLinear n E) := borel _
  have _ : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let _ : MeasurableSpace (B.Levi E) := borel _
  have _ : BorelSpace (B.Levi E) := ⟨rfl⟩
  -- The integer ring of `E` and the compact open subgroups used for normalization.
  let O : Subring E := (ValuativeRel.valuation E).integer
  have hOc : IsCompact (O : Set E) := (LocalFieldData.ofInstances E).isCompact_integers
  have hOo : IsOpen (O : Set E) := (LocalFieldData.ofInstances E).isOpen_integers
  have hKc : ∀ r : ℕ, IsCompact (GeneralLinearGroup.integralSubgroup (Fin r) O :
      Set (GeneralLinear r E)) := fun r =>
    GeneralLinearGroup.isCompact_integralSubgroup (Fin r) O hOc
  have hKo : ∀ r : ℕ, IsOpen (GeneralLinearGroup.integralSubgroup (Fin r) O :
      Set (GeneralLinear r E)) := fun r =>
    GeneralLinearGroup.isOpen_integralSubgroup (Fin r) O hOo
  let K := GeneralLinearGroup.integralSubgroup (Fin n) O
  -- Normalized Haar measures.
  obtain ⟨μG, hμG, hμG1⟩ := exists_isHaarMeasure_eq_one (G := GeneralLinear n E) (hKc n)
    (by rw [(hKo n).interior_eq]; exact ⟨1, K.one_mem⟩)
  have hMOeq : {x : B.Levi E | ∀ i, x i ∈ GeneralLinearGroup.integralSubgroup (Fin (B.size i)) O}
      = Set.univ.pi fun i => (GeneralLinearGroup.integralSubgroup (Fin (B.size i)) O :
        Set (GeneralLinear (B.size i) E)) := by
    ext x
    simp
  have hMOc : IsCompact {x : B.Levi E | ∀ i, x i ∈
      GeneralLinearGroup.integralSubgroup (Fin (B.size i)) O} := by
    rw [hMOeq]
    exact isCompact_univ_pi fun i => hKc (B.size i)
  have hMOo : IsOpen {x : B.Levi E | ∀ i, x i ∈
      GeneralLinearGroup.integralSubgroup (Fin (B.size i)) O} := by
    rw [hMOeq]
    exact isOpen_set_pi Set.finite_univ fun i _ => hKo (B.size i)
  obtain ⟨μM, hμM, hμM1⟩ := exists_isHaarMeasure_eq_one (G := B.Levi E) hMOc
    (by rw [hMOo.interior_eq]; exact ⟨1, fun i => (GeneralLinearGroup.integralSubgroup
      (Fin (B.size i)) O).one_mem⟩)
  have hUcl : IsClosed (B.unipotentSubgroup E : Set (GeneralLinear n E)) :=
    B.isClosed_unipotentSubgroup E
  have hUOc : IsCompact {y : B.unipotentSubgroup E | (y : GeneralLinear n E) ∈ K} :=
    hUcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hKc n)
  have hUOo : IsOpen {y : B.unipotentSubgroup E | (y : GeneralLinear n E) ∈ K} :=
    (hKo n).preimage continuous_subtype_val
  obtain ⟨μU, hμU, hμU1⟩ := exists_isHaarMeasure_eq_one (G := B.unipotentSubgroup E) hUOc
    (by rw [hUOo.interior_eq]; exact ⟨1, K.one_mem⟩)
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hKc n)
  obtain ⟨μK, hμK, hμK1⟩ := exists_isHaarMeasure_isProbabilityMeasure (G := K)
  -- Windows for the Levi values on their twisted conjugacy saturations.
  have hvalue := fun j => (hb j).exists_saturation (leviTensorIntertwiner_comp σ B A) μM
  choose Ω hΩo hΩd hΩv using hvalue
  obtain ⟨U₀, hU₀o, hδU₀, hU₀⟩ := hLD F E σ l n hE hn B δ γ hδγ hγ k m hm d hd μG μM μU μK
    hμG1 hμM1 hμU1 Ω hΩo hΩd
  apply hasTwistedCharacterValue_of_hasLocalValue
  refine ⟨μG, hμG, U₀, hU₀o, hδU₀, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψs, hψi, hψf⟩ := hU₀ φ hφ
  have hΨ : ∀ x : B.Levi E, (∑ j, ψ j) x =
      ((LocalFieldData.ofInstances E).leviHalfModulus B x : ℂ) *
        ∫ y, ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ * B.leviEmbedding E x *
          (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK ∂μU := by
    intro x
    rw [← hψf x, Submodule.coe_sum, Finset.sum_apply]
  rw [hVD F E σ n B W P hP A μG μM μU μK hμG1 hμM1 hμU1 φ (∑ j, ψ j) hΨ, map_sum]
  have hterm : ∀ j, twistedDistribution μM (B.blockTensor P)
      (FiniteTensor.isAdmissible_external P hP) (leviTensorIntertwiner σ B A).toLinearMap (ψ j) =
      relativeDiscriminantWeight B (m j) * b j * ∫ g, φ g ∂μG := by
    intro j
    rw [hΩv j (ψ j) (hψs j), hψi j]
    have hnorm : cyclicNorm σ l (B.leviEmbedding E (d j)) =
        baseChange F E n (B.leviEmbedding F (m j)) := by
      rw [cyclicNorm_leviEmbedding, baseChange_leviEmbedding]
      congr 1
      funext i
      exact (hd j).2 i
    have hdisc := twistedRelativeParabolicDiscriminant_eq_of_cyclicNorm B hE hnorm
    simp only [relativeDiscriminantWeight]
    rw [hdisc]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul]

end Reduction

end Langlands.BaseChange
