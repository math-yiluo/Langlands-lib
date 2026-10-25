import Langlands.Representation.Classification.Tempered

/-!
# A fixed real exponent for coefficients modulo the center

This predicate isolates the common coefficient condition used at exponent `2`
for square-integrability and at each exponent `2 + ε` for temperedness.
-/

namespace Langlands

universe uG uV uF

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- Admissibility and a unitary central character whose every absolute smooth
coefficient belongs to `L^r` on the actual central quotient. -/
def IsLpModCenter (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] (r : ℝ) : Prop :=
  IsAdmissible ρ ∧ ∃ c : UnitaryCentralCharacter ρ,
    ∀ (ℓ : SmoothDual ρ) (v : V),
      MeasureTheory.MemLp (c.coefficientNorm ℓ v) (ENNReal.ofReal r) μ

/-- At exponent two the fixed-exponent predicate is the existing
square-integrability predicate. -/
theorem isLpModCenter_two_iff [IsTopologicalGroup G]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (ρ : Representation ℂ G V)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsLpModCenter ρ μ 2 ↔ IsSquareIntegrableModCenter ρ μ := by
  simp only [IsLpModCenter, IsSquareIntegrableModCenter, ENNReal.ofReal_ofNat]

end Generic

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The fixed-exponent condition for every Haar measure on the canonical Borel
realization of the actual central quotient of `GL_n(F)`. -/
def IsLp (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (r : ℝ) : Prop :=
  letI := T.topology
  haveI := T.generalLinearTopologicalGroup n
  letI := T.centralQuotientMeasurableSpace n
  haveI := T.centralQuotientBorelSpace n
  ∀ (μ : MeasureTheory.Measure
      (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
    [MeasureTheory.Measure.IsHaarMeasure μ], IsLpModCenter ρ μ r

/-- The canonical all-Haar predicate at exponent two agrees with the existing
square-integrability predicate. -/
theorem isLp_two_iff (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    T.IsLp ρ 2 ↔ T.IsSquareIntegrable ρ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  exact forall_congr' fun μ => forall_congr' fun _ =>
    isLpModCenter_two_iff ρ μ

end PadicField.TopologicalData

end Langlands
