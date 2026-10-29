import Langlands.Group.GL.LowerTriangularQuotientCell
import Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport

/-!
# Quotient measures on the open lower-triangular cell

A right-invariant quotient measure on `N_m \ GL_m` that is finite on compacts
pulls back along the open cell `B⁻_m → N_m \ GL_m` to a right-invariant measure on
`B⁻_m`, finite on compacts, whose pushforward recovers the quotient measure when
the cell is conull. Nonzero right-invariant measures finite on compacts on a
second countable locally compact group differ by a positive scalar.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory Measure Topology Set GeneralLinear QuotientIntegration
open scoped ENNReal NNReal

universe u uF

section Uniqueness

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Uniqueness of right-invariant measures: two nonzero right-invariant
measures, finite on compacts, on a second countable locally compact group are
positive real multiples of each other. -/
theorem exists_pos_smul_eq_of_isMulRightInvariant (ρ₁ ρ₂ : Measure G)
    [IsFiniteMeasureOnCompacts ρ₁] [IsFiniteMeasureOnCompacts ρ₂]
    [ρ₁.IsMulRightInvariant] [ρ₂.IsMulRightInvariant] (h₁ : ρ₁ ≠ 0) (h₂ : ρ₂ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ρ₁ = ENNReal.ofReal C • ρ₂ := by
  have e₁ : ρ₁.inv = haarScalarFactor ρ₁.inv (haar : Measure G) • haar :=
    isMulLeftInvariant_eq_smul _ _
  have e₂ : ρ₂.inv = haarScalarFactor ρ₂.inv (haar : Measure G) • haar :=
    isMulLeftInvariant_eq_smul _ _
  set c₁ := haarScalarFactor ρ₁.inv (haar : Measure G)
  set c₂ := haarScalarFactor ρ₂.inv (haar : Measure G)
  have hinv_smul : ∀ (c : ℝ≥0) (ν : Measure G), (c • ν).inv = c • ν.inv := by
    intro c ν
    rw [Measure.inv_def, Measure.inv_def, Measure.map_smul]
    exact measurable_inv.aemeasurable
  have hc : ∀ (ρ : Measure G) (c : ℝ≥0), ρ ≠ 0 → ρ.inv = c • haar → c ≠ 0 := by
    intro ρ c hρ e hc0
    apply hρ
    rw [← Measure.inv_inv ρ, e, hc0, zero_smul, Measure.inv_def, Measure.map_zero]
  have hc₁ := hc ρ₁ c₁ h₁ e₁
  have hc₂ := hc ρ₂ c₂ h₂ e₂
  refine ⟨((c₁ / c₂ : ℝ≥0) : ℝ), by positivity, ?_⟩
  rw [ENNReal.ofReal_coe_nnreal]
  calc ρ₁ = ρ₁.inv.inv := (Measure.inv_inv ρ₁).symm
    _ = (c₁ • (haar : Measure G)).inv := by rw [e₁]
    _ = ((c₁ / c₂) • ρ₂.inv).inv := by
        rw [e₂, smul_smul, div_mul_cancel₀ _ hc₂]
    _ = (c₁ / c₂ : ℝ≥0) • ρ₂ := by
        rw [hinv_smul, Measure.inv_inv]

end Uniqueness

section Cell

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The cell map intertwines right multiplication in `B⁻_m` with right
translation of cosets. -/
theorem lowerTriangularQuotientMap_mul (T : F.TopologicalData) (m : ℕ)
    (b c : lowerTriangularSubgroup m F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    lowerTriangularQuotientMap m F.Carrier (b * c) =
      rightTranslate (upperUnipotent m F.Carrier) c.val
        (lowerTriangularQuotientMap m F.Carrier b) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  rfl

/-- The cell map is a measurable embedding for the Borel structures. -/
theorem lowerTriangularQuotientMap_measurableEmbedding (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    letI := borel (lowerTriangularSubgroup m F.Carrier)
    letI := borel (LeftQuotient (upperUnipotent m F.Carrier))
    MeasurableEmbedding (lowerTriangularQuotientMap m F.Carrier) := by
  let := T.topology
  let := borel (lowerTriangularSubgroup m F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup m F.Carrier) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent m F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent m F.Carrier)) := ⟨rfl⟩
  exact (isOpenEmbedding_lowerTriangularQuotientMap T m).measurableEmbedding

/-- Pullback of a right-invariant quotient measure, finite on compacts, to the
lower triangular group: it is right invariant and finite on compacts, and when
the cell is conull its pushforward is the quotient measure. -/
theorem comap_lowerTriangularQuotientMap_properties (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    letI := borel (lowerTriangularSubgroup m F.Carrier)
    letI := borel (LeftQuotient (upperUnipotent m F.Carrier))
    ∀ (μ : Measure (LeftQuotient (upperUnipotent m F.Carrier))),
      IsFiniteMeasureOnCompacts μ →
      (∀ g, MeasurePreserving (rightTranslate (upperUnipotent m F.Carrier) g) μ μ) →
      let ρ := μ.comap (lowerTriangularQuotientMap m F.Carrier)
      ρ.IsMulRightInvariant ∧ IsFiniteMeasureOnCompacts ρ ∧
        (μ (range (lowerTriangularQuotientMap m F.Carrier))ᶜ = 0 →
          ρ.map (lowerTriangularQuotientMap m F.Carrier) = μ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  let := borel (lowerTriangularSubgroup m F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup m F.Carrier) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent m F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent m F.Carrier)) := ⟨rfl⟩
  intro μ hμ hinv ρ
  have hβ := lowerTriangularQuotientMap_measurableEmbedding (F := F) T m
  have hβc : Continuous (lowerTriangularQuotientMap m F.Carrier) :=
    (isOpenEmbedding_lowerTriangularQuotientMap T m).continuous
  refine ⟨⟨fun c => ?_⟩, ⟨fun K hK => ?_⟩, fun hnull => ?_⟩
  · ext S hS
    rw [Measure.map_apply (measurable_mul_const c) hS, hβ.comap_apply, hβ.comap_apply]
    have himage : lowerTriangularQuotientMap m F.Carrier '' ((fun x => x * c) ⁻¹' S) =
        rightTranslate (upperUnipotent m F.Carrier) c.val ⁻¹'
          (lowerTriangularQuotientMap m F.Carrier '' S) := by
      ext q
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b * c, hb, lowerTriangularQuotientMap_mul T m b c⟩
      · rintro ⟨b, hb, hq⟩
        refine ⟨b * c⁻¹, by simpa using hb, ?_⟩
        have := congrArg (rightTranslate (upperUnipotent m F.Carrier) c⁻¹.val) hq
        rw [← lowerTriangularQuotientMap_mul, rightTranslate_mul] at this
        simpa using this
    rw [himage]
    exact (hinv c.val).measure_preimage (hβ.measurableSet_image.mpr hS).nullMeasurableSet
  · rw [hβ.comap_apply]
    exact (hK.image hβc).measure_lt_top
  · rw [hβ.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp hnull |>.mono
      fun q hq => by simpa using hq)

end Cell

end Langlands.RankinSelberg
