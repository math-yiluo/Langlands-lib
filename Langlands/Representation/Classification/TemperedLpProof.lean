import Langlands.Representation.Classification.TemperedLpStatement

namespace Langlands

universe uG uF uV

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace (G ⧸ Subgroup.center G)]

theorem isTemperedModCenter_iff_forall_isLp
    (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsTemperedModCenter ρ μ ↔
      ∀ (ε : ℝ), 0 < ε → IsLpModCenter ρ μ (2 + ε) := by
  constructor
  · rintro ⟨hρ, c, hc⟩ ε hε
    exact ⟨hρ, c, fun ℓ v => hc ℓ v ε hε⟩
  · intro h
    obtain ⟨hρ, c, _⟩ := h 1 zero_lt_one
    refine ⟨hρ, c, ?_⟩
    intro ℓ v ε hε
    obtain ⟨_, d, hd⟩ := h ε hε
    rw [c.coefficientNorm_eq d]
    exact hd ℓ v

end Generic

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem isTempered_iff_forall_isLp
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T.IsTempered ρ ↔ ∀ (ε : ℝ), 0 < ε → T.IsLp ρ (2 + ε) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  constructor
  · intro h ε hε μ _
    exact (isTemperedModCenter_iff_forall_isLp ρ μ).mp (h μ) ε hε
  · intro h μ _
    apply (isTemperedModCenter_iff_forall_isLp ρ μ).mpr
    intro ε hε
    exact h ε hε μ

end PadicField.TopologicalData

/-- The two fixed-exponent descriptions of temperedness. -/
theorem temperedLp.{uGroup, uField, uCarrier} :
    TemperedLpStatement.{uGroup, uField, uCarrier} := by
  constructor
  · intro G _ _ V _ _ _ ρ μ _
    exact isTemperedModCenter_iff_forall_isLp ρ μ
  · intro p _ F T n V _ _ ρ
    exact T.isTempered_iff_forall_isLp ρ

end Langlands
