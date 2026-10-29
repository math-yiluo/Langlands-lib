import Langlands.Representation.RankinSelberg.InducedTailIntermediateDiagonalExtensionSpanStatement
import Langlands.Representation.RankinSelberg.InducedTailIntermediateInverseCharacterStatement
import Langlands.Representation.RankinSelberg.InducedTailIntermediateZeroRowTail
import Langlands.Representation.RankinSelberg.InducedTailIntermediatePointwise
import Langlands.Representation.RankinSelberg.InducedTailIntermediateDisintegrationTransfer
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCanonicalMeasures
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence

/-! # Assembly with exact intermediate-tail prerequisites -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear MeasureTheory Whittaker HarmonicAnalysis QuotientIntegration

universe uF uV uV₁ uV₂ uW

private theorem twoBlock_type_of_statement
    (htype : NormalizedProductWhittakerTypeStatement.{uF, uV})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (a b : ℕ) {V₁ V₂ : Type uV}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (h₁ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁)
    (h₂ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType (a + 1 + b) (standardCharacter ψ (a + 1 + b))
      (F.canonicalNormalizedProductInduced
        (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
        (Shahidi.pairFamily π₁ π₂)) := by
  let := F.canonicalTopologicalData.topology
  let m : Fin 2 → ℕ := ![a, b]
  have hm : ∑ i, (m i + 1) = (a + 1 + b) + 1 := by
    simp only [m, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  let σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier)
      (Shahidi.pairCarrier V₁ V₂ i) := fun i =>
    match i with
    | 0 => π₁
    | 1 => π₂
  have hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i) := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
  have h0 := htype p F ψ (a + 1 + b) 2 m hm σ hσ
  let D := Σ s : {s : Fin 2 → ℕ // (∀ i, 0 < s i) ∧
      ∑ i, s i = (a + 1 + b) + 1},
    ∀ i, Representation ℂ (Langlands.GeneralLinear (s.val i) F.Carrier)
      (Shahidi.pairCarrier V₁ V₂ i)
  let d₀ : D := ⟨⟨fun i => m i + 1, ⟨fun i => Nat.succ_pos _, hm⟩⟩, σ⟩
  let d₁ : D := ⟨⟨![a + 1, b + 1],
    ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
      by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega⟩⟩,
    Shahidi.pairFamily π₁ π₂⟩
  have hd : d₀ = d₁ := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      fin_cases i <;> rfl
  let P : D → Prop := fun d =>
    IsOfWhittakerType (a + 1 + b) (standardCharacter ψ (a + 1 + b))
      (F.canonicalNormalizedProductInduced
        ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2)
  change P d₀ at h0
  change P d₁
  rwa [← hd]

private def representationRankCast {F : Type uF} [Field F] {m n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (h : m = n)
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F) V := h ▸ π

private theorem type_rankCast {F : Type uF} [Field F] [TopologicalSpace F]
    (ψ : UnitaryAdditiveCharacter F) {m n : ℕ} (h : m = n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (hπ : IsOfWhittakerType m (standardCharacter ψ m) π) :
    IsOfWhittakerType n (standardCharacter ψ n) (h ▸ π) := by
  subst n
  exact hπ

private theorem valuesAt_block_eq {F : Type uF} [Field F] [TopologicalSpace F]
    {r n j k l : ℕ} (h : k = l)
    (hk : r = n + (j + k + 1)) (hl : r = n + (j + l + 1))
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    unequalRankZetaValuesAt j k hk q ψ abv μ ν π σ =
      unequalRankZetaValuesAt j l hl q ψ abv μ ν π σ := by
  subst l
  rfl

private theorem valuesAt_rankCast {F : Type uF} [Field F] [TopologicalSpace F]
    {r m n : ℕ} (hm : r = m) (j k : ℕ) (hk : m = n + (j + k + 1))
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) :
    unequalRankZetaValuesAt j k (hm.trans hk) q ψ abv μ ν π σ =
      unequalRankZetaValues q ψ abv j k μ ν (hk ▸ (hm ▸ π)) σ := by
  subst hm
  subst hk
  rfl

set_option maxHeartbeats 1200000 in
/-- Assemble the unchanged intermediate-tail span from the five exact
prerequisite statements, retained in their published order and universes. -/
theorem intermediateRankSpan_of_exact_prerequisites
    (hspan : InducedTailIntermediateDiagonalExtensionSpanStatement.{uF,
      max uF uV₁ uV₂, uW})
    (hext : TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂})
    (htype : NormalizedProductWhittakerTypeStatement.{uF, max uV₁ uV₂})
    (hdis : LowerBlockQuotientDisintegrationStatement.{uF})
    (hinv : InducedTailIntermediateInverseCharacterStatement.{uF, uW, uV₂}) :
    InducedTailIntermediateRankSpanStatement.{uF, uV₁, uV₂, uW} := by
  intro p _ F ψ ν a b t V₁ _ _ V₂ _ _ E _ _ π₁ π₂ σ hπ₁ hπ₂ hσ
  dsimp only
  intro hBT hTr
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = b + (k + 1) := ⟨t - b - 1, by omega⟩
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.valuativeExtension
  let := F.canonicalTopologicalData.moduleTopology
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (b + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (b + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (b + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (b + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient b F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient b F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (b + (k + 1) + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (b + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (b + (k + 1) + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (b + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (b + (k + 1)) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (b + (k + 1)) F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
  let : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
  intro hrightTail hrightFull μtail μfull htail hfull
  let η : AdditiveHaarMeasure F.Carrier := ν.val
  let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
      (ULift.{uV₂} V₁) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
  let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
      (ULift.{uV₁} V₂) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
  let ξ := F.canonicalNormalizedProductInduced
    (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
    (Shahidi.pairFamily π₁' π₂')
  have e₁ : π₁.Equiv π₁' := Representation.Equiv.mk ULift.moduleEquiv.symm
    (fun g => by ext v; rfl)
  have e₂ : π₂.Equiv π₂' := Representation.Equiv.mk ULift.moduleEquiv.symm
    (fun g => by ext v; rfl)
  have hξ : IsOfWhittakerType (a + 1 + b) (standardCharacter ψ (a + 1 + b)) ξ :=
    twoBlock_type_of_statement htype p F ψ a b π₁' π₂'
      (hπ₁.of_equiv e₁) (hπ₂.of_equiv e₂)
  let c₀ := a + 1 + b - (b + (k + 1)) - 1
  have ha : a + 1 = (k + 1) + (c₀ + 1) := by dsimp [c₀]; omega
  have hRank : a + 1 + b = b + 1 + (k + 1) + c₀ := by omega
  let ξc : Representation ℂ
      (Langlands.GeneralLinear ((b + 1) + (k + 1) + (c₀ + 1)) F.Carrier) _ :=
    representationRankCast hRank ξ
  have hξc : IsOfWhittakerType (b + 1 + (k + 1) + c₀)
      (standardCharacter ψ (b + 1 + (k + 1) + c₀)) ξc :=
    type_rankCast ψ hRank ξ hξ
  have hk : b + (k + 1) - b - 1 = k := by omega
  have hTailRank : b + (k + 1) = b + (0 + k + 1) := by omega
  have hFullRank : a + 1 + b = (b + (k + 1)) + (0 + c₀ + 1) := by omega
  change zetaSpan (unequalRankZetaValuesAt 0 (b + (k + 1) - b - 1) (by omega)
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μtail
      (rectangularMeasure η 0 (b + 1)) σ π₂) ≤
    zetaSpan (unequalRankZetaValuesAt 0 c₀ hFullRank
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μfull
      (rectangularMeasure η 0 (b + (k + 1) + 1)) ξ σ)
  rw [valuesAt_block_eq hk (by omega) hTailRank
    F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) μtail
    (rectangularMeasure η 0 (b + 1)) σ π₂]
  let : SigmaFinite μtail :=
    compatible_quotientMeasure_sigmaFinite F.canonicalTopologicalData b μtail htail
  obtain ⟨hrectσ, _, _, hrectpos, hrectfc⟩ :=
    rectangularMeasure_analytic_properties F.canonicalTopologicalData
      (k + 1) (b + 1) η
  let : SigmaFinite (rectangularMeasure η (k + 1) (b + 1)) := hrectσ
  let : (rectangularMeasure η (k + 1) (b + 1)).IsOpenPosMeasure := hrectpos
  let : IsFiniteMeasureOnCompacts (rectangularMeasure η (k + 1) (b + 1)) := hrectfc
  let D := disintegrationDataOfStatement hdis p F b k η μtail μfull htail hfull
  let : SigmaFinite D.triangularMeasure := D.sigmaFinite
  let : D.triangularMeasure.IsOpenPosMeasure := D.openPos
  let : IsFiniteMeasureOnCompacts D.triangularMeasure := D.finiteOnCompacts
  apply Submodule.span_le.2
  intro R hR
  rw [hinv p F F.canonicalTopologicalData b (b + (k + 1)) 0 k hTailRank
    ψ η μtail μtail htail htail σ π₂] at hR
  obtain ⟨Wtest, hWtest, Wtail, hWtail, A, hconv, hcont⟩ :=
    exists_reversedTail_of_mem_scaled F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μtail η k
      rfl hTailRank σ π₂ hR
  have hextall : ∀ Φ : SchwartzBruhat (Fin (b + 1) → F.Carrier),
      ∃ W ∈ whittakerSet ψ (b + 1 + (k + 1) + c₀) ξc,
        ∀ g : Langlands.GeneralLinear (b + 1) F.Carrier,
          W.val (lowerBlockLocalization (c₀ + 1) g 0 1) =
            Wtail.val g * Φ (lastRow g) *
              (Real.rpow
                (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                ((((k + 1) + (c₀ + 1) : ℕ) : ℝ) / 2) : ℂ) := by
    intro Φ
    obtain ⟨W, hW, hformula⟩ :=
      exists_canonical_diagonal_extension_of_extension hext p F ψ a b (k + 1) c₀ ha
        π₁ π₂ hπ₁ hπ₂ Wtail hWtail Φ
    refine ⟨whittakerRankCast ψ hRank W, whittakerRankCast_mem ψ hRank ξ hW, ?_⟩
    intro g
    simpa only [whittakerRankCast_apply] using hformula g
  have hmem := hspan p F b (k + 1) c₀ k rfl ψ _ ξc hξc Wtail _ σ hσ.1.1
    Wtest hWtest hextall μtail μfull (rectangularMeasure η (k + 1) (b + 1))
    D.triangularMeasure D.normalization D.normalization_pos D.transfer R A hconv hcont
  have hgap : b + 1 + (k + 1) + c₀ = (b + (k + 1)) + (0 + c₀ + 1) := by omega
  rw [valuesAt_rankCast hRank 0 c₀ hgap, rectangularMeasure_zero_rows]
  exact hmem

end Langlands.RankinSelberg.InducedTailIntermediate
