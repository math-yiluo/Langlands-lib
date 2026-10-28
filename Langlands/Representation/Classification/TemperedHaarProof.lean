import Langlands.Representation.Classification.TemperedHaarStatement
import Langlands.Analysis.HaarLpProof
import Langlands.Group.GL.CentralQuotientTopologyProof

/-! # Haar-choice invariance for analytic temperedness on actual GL groups and Levis -/

namespace Langlands

universe uG uF uV

-- Both measurable-space binders are needed to express cross-Borel transport.
set_option linter.overlappingInstances false in
private theorem extendTemperedHaar
    (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup (G ⧸ Subgroup.center G)]
    [LocallyCompactSpace (G ⧸ Subgroup.center G)]
    [SecondCountableTopology (G ⧸ Subgroup.center G)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ∀ [MeasurableSpace (G ⧸ Subgroup.center G)]
      [BorelSpace (G ⧸ Subgroup.center G)]
      (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
      [MeasureTheory.Measure.IsHaarMeasure μ],
      IsTemperedModCenter ρ μ →
        ∀ [MeasurableSpace (G ⧸ Subgroup.center G)]
          [BorelSpace (G ⧸ Subgroup.center G)]
          (ν : MeasureTheory.Measure (G ⧸ Subgroup.center G))
          [MeasureTheory.Measure.IsHaarMeasure ν],
          IsTemperedModCenter ρ ν := by
  intro m₀ b₀ μ hμ h m₁ b₁ ν hν
  have hm : m₁ = m₀ := b₁.measurable_eq.trans b₀.measurable_eq.symm
  subst m₁
  obtain ⟨hρ, c, hc⟩ := h
  refine ⟨hρ, c, fun ℓ v ε hε => ?_⟩
  exact (haarMemLpInvariant _ μ ν (c.coefficientNorm ℓ v)
    (ENNReal.ofReal (2 + ε))).mp (hc ℓ v ε hε)

private theorem glTemperedFixedHaarAux : GLTemperedFixedHaarStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n
  dsimp only
  obtain ⟨hQgroup, _, hQcompact, hQcountable, _⟩ :=
    (glBlockCentralQuotientTopology p F T n).1
  let _ := hQgroup
  let _ := hQcompact
  let _ := hQcountable
  intro m b μ hμ V _ _ ρ
  have hm : m = T.centralQuotientMeasurableSpace n := b.measurable_eq
  subst m
  let := T.centralQuotientMeasurableSpace n
  let := T.centralQuotientBorelSpace n
  constructor
  · intro h
    exact h μ
  · intro h ν _
    obtain ⟨hρ, c, hc⟩ := h
    refine ⟨hρ, c, fun ℓ v ε hε => ?_⟩
    exact (haarMemLpInvariant _ μ ν (c.coefficientNorm ℓ v)
      (ENNReal.ofReal (2 + ε))).mp (hc ℓ v ε hε)

private theorem glLeviTemperedHaarExtensionAux :
    GLLeviTemperedHaarExtensionStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n B
  dsimp only
  obtain ⟨hQgroup, _, hQcompact, hQcountable, _⟩ :=
    (glBlockCentralQuotientTopology p F T n).2 B
  let _ := hQgroup
  let _ := hQcompact
  let _ := hQcountable
  intro m₀ b₀ μ hμ V _ _ σ ht m₁ b₁ ν hν
  exact @extendTemperedHaar (B.Levi F.Carrier) _ _ _ _ _ V _ _ σ
    m₀ b₀ μ hμ ht m₁ b₁ ν hν

/-- The Library's actual GL and product-Levi analytic temperedness predicates
may be tested at one arbitrary Borel Haar measure. -/
theorem glTemperedHaar : GLTemperedHaarStatement.{uF, uV} :=
  ⟨glTemperedFixedHaarAux, glLeviTemperedHaarExtensionAux⟩

/-- The ambient GL fixed-Haar component. -/
theorem glTemperedFixedHaar : GLTemperedFixedHaarStatement.{uF, uV} :=
  glTemperedHaar.1

/-- Extension across arbitrary Borel Haar realizations for actual product Levis. -/
theorem glLeviTemperedHaarExtension :
    GLLeviTemperedHaarExtensionStatement.{uF, uV} :=
  glTemperedHaar.2

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The universal-Haar GL predicate at any supplied Borel Haar realization. -/
theorem isTempered_iff_fixedHaar
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    ∀ [MeasurableSpace
        (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier))]
      [BorelSpace
        (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier))]
      (μ : MeasureTheory.Measure
        (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
      [MeasureTheory.Measure.IsHaarMeasure μ],
      T.IsTempered ρ ↔ IsTemperedModCenter ρ μ := by
  let := T.topology
  intro _ _ μ _
  exact glTemperedFixedHaar p F T n μ V ρ

end PadicField.TopologicalData

namespace RelativeRegularComparison

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The all-Borel, all-Haar product-Levi predicate is equivalent to its value
at any one supplied Borel Haar measure of the same actual full central quotient. -/
theorem isLeviTempered_iff_fixedHaar (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    letI := T.topology
    ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : MeasureTheory.Measure (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
      [MeasureTheory.Measure.IsHaarMeasure μ],
      IsLeviTempered T B σ ↔ IsTemperedModCenter σ.ρ μ := by
  let := T.topology
  intro m₀ b₀ μ hμ
  constructor
  · intro h
    exact h μ
  · intro h m₁ b₁ ν hν
    exact @glLeviTemperedHaarExtension p _ F T n B m₀ b₀ μ hμ
      σ _ _ σ.ρ h m₁ b₁ ν hν

end RelativeRegularComparison

end Langlands
