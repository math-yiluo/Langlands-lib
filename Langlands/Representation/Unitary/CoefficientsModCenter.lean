import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Category.Contragredient
import Langlands.Analysis.HaarLpProof
import Langlands.Group.GL.CentralQuotientTopologyProof

/-!
# Invariant-form coefficients on the actual central quotient

The comparison concerns the algebraic smooth representation and its form.
It does not identify arbitrary vectors in a Hilbert completion.
-/

noncomputable section

namespace Langlands

universe uG uV uF

namespace InvariantPositiveForm

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V}

/-- The actual absolute form coefficient descended to the quotient by the center. -/
def coefficientNorm (b : InvariantPositiveForm ρ) (c : UnitaryCentralCharacter ρ)
    (w v : V) : G ⧸ Subgroup.center G → ℝ :=
  c.coefficientNorm (b.rightFunctional w) v

@[simp]
theorem coefficientNorm_mk (b : InvariantPositiveForm ρ) (c : UnitaryCentralCharacter ρ)
    (w v : V) (g : G) :
    b.coefficientNorm c w v (QuotientGroup.mk g) = ‖b.inner w (ρ g v)‖ := rfl

/-- The descended form coefficient is independent of the central-character witness. -/
theorem coefficientNorm_eq (b : InvariantPositiveForm ρ)
    (c d : UnitaryCentralCharacter ρ) (w v : V) :
    b.coefficientNorm c w v = b.coefficientNorm d w v :=
  c.coefficientNorm_eq d (b.rightFunctional w) v

variable [IsTopologicalGroup G]
variable [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- All smooth-dual coefficients have `MemLp` exactly when all form coefficients
do, using admissibility and compact-open cofinality for the reverse direction. -/
theorem forall_memLp_coefficientNorm_iff (b : InvariantPositiveForm ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsAdmissible ρ) (c : UnitaryCentralCharacter ρ)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)) (r : ENNReal) :
    (∀ (ℓ : SmoothDual ρ) (v : V), MeasureTheory.MemLp (c.coefficientNorm ℓ v) r μ) ↔
      ∀ (w v : V), MeasureTheory.MemLp (b.coefficientNorm c w v) r μ := by
  constructor
  · intro h w v
    exact h (b.toSmoothDual hρ.1 w) v
  · intro h ℓ v
    obtain ⟨w, hw⟩ := b.toSmoothDual_surjective hcofinal hρ ℓ
    rw [← hw]
    exact h w v

variable [BorelSpace (G ⧸ Subgroup.center G)]

/-- The Library's smooth-dual square-integrability predicate is equivalent to
the form-coefficient criterion on the same actual central quotient. -/
theorem isSquareIntegrableModCenter_iff (b : InvariantPositiveForm ρ)
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    IsSquareIntegrableModCenter ρ μ ↔
      IsAdmissible ρ ∧ ∃ c : UnitaryCentralCharacter ρ,
        ∀ w v : V, MeasureTheory.MemLp (b.coefficientNorm c w v) 2 μ := by
  constructor
  · rintro ⟨hρ, c, hc⟩
    exact ⟨hρ, c, (b.forall_memLp_coefficientNorm_iff hcofinal hρ c μ 2).mp hc⟩
  · rintro ⟨hρ, c, hc⟩
    exact ⟨hρ, c, (b.forall_memLp_coefficientNorm_iff hcofinal hρ c μ 2).mpr hc⟩

end InvariantPositiveForm

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For every Borel Haar measure, square-integrability with that fixed measure
is equivalent to the universal-Haar predicate in the Library. -/
theorem isSquareIntegrable_iff_fixedHaar
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    letI := T.centralQuotientMeasurableSpace n
    haveI := T.centralQuotientBorelSpace n
    haveI := T.generalLinearTopologicalGroup n
    ∀ (μ : MeasureTheory.Measure
        (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
      [MeasureTheory.Measure.IsHaarMeasure μ],
      T.IsSquareIntegrable ρ ↔ IsSquareIntegrableModCenter ρ μ := by
  let := T.topology
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  have := T.generalLinearTopologicalGroup n
  obtain ⟨hQgroup, _, hQcompact, hQcountable, _⟩ :=
    (glBlockCentralQuotientTopology p F T n).1
  let _ := hQgroup
  let _ := hQcompact
  let _ := hQcountable
  intro μ _
  constructor
  · intro h
    exact h μ
  · intro h ν _
    obtain ⟨hρ, c, hc⟩ := h
    refine ⟨hρ, c, fun ℓ v => ?_⟩
    exact (haarMemLpInvariant _ μ ν (c.coefficientNorm ℓ v) 2).mp (hc ℓ v)

/-- The exact p-adic universal-Haar predicate can be checked on invariant-form
coefficients for any one Borel Haar measure on the actual central quotient. -/
theorem isSquareIntegrable_iff_formCoefficients
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (b : InvariantPositiveForm ρ) :
    letI := T.topology
    letI := T.centralQuotientMeasurableSpace n
    haveI := T.centralQuotientBorelSpace n
    ∀ (μ : MeasureTheory.Measure
        (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
      [MeasureTheory.Measure.IsHaarMeasure μ],
      T.IsSquareIntegrable ρ ↔
        IsAdmissible ρ ∧ ∃ c : UnitaryCentralCharacter ρ,
          ∀ w v : V, MeasureTheory.MemLp (b.coefficientNorm c w v) 2 μ := by
  let := T.topology
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  have := T.generalLinearTopologicalGroup n
  intro μ _
  exact (T.isSquareIntegrable_iff_fixedHaar ρ μ).trans
    (b.isSquareIntegrableModCenter_iff (GeneralLinear.compactOpen_cofinal F T n) μ)

end PadicField.TopologicalData
end Langlands
