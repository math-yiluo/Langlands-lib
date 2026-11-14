import Langlands.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure
import Langlands.AllField.Group.GL.LowerTriangularQuotientCell
import Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport
/-!
# Quotient measures on the open lower-triangular cell

A right-invariant quotient measure on `N_m \ GL_m` that is finite on compacts
pulls back along the open cell `B⁻_m → N_m \ GL_m` to a right-invariant measure on
`B⁻_m`, finite on compacts, whose pushforward recovers the quotient measure when
the cell is conull. Nonzero right-invariant measures finite on compacts on a
second countable locally compact group differ by a positive scalar.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LowerBlockQuotientDisintegrationStatement comap_lowerTriangularQuotientMap_properties continuous_lowerBlockQuotientDensity lowerBlockDensity_unipotent_mul lowerBlockQuotientDensity lowerBlockQuotientDensity_mk lowerTriangularQuotientMap_measurableEmbedding lowerTriangularQuotientMap_mul lowerTriangularRightHaar lowerTriangularRightHaar_properties measurable_lowerBlockQuotientDensity rectangularMeasure_compactOpen_pos_lt_top
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory Measure _root_.Topology Set
open Langlands.GeneralLinear hiding exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular isOpenEmbedding_lowerTriangularQuotientMap isOpen_upperUnipotent_mul_lowerTriangular_inter
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal NNReal

universe u uF

section Uniqueness


end Uniqueness

section Cell

variable {F : Type uF} [Field F]

/-- The cell map intertwines right multiplication in `B⁻_m` with right
translation of cosets. -/
theorem lowerTriangularQuotientMap_mul (T : LocalFieldData F) (m : ℕ)
    (b c : lowerTriangularSubgroup m F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    lowerTriangularQuotientMap m F (b * c) =
      rightTranslate (upperUnipotent m F) c.val
        (lowerTriangularQuotientMap m F b) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  rfl

/-- The cell map is a measurable embedding for the Borel structures. -/
theorem lowerTriangularQuotientMap_measurableEmbedding (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    letI := borel (lowerTriangularSubgroup m F)
    letI := borel (LeftQuotient (upperUnipotent m F))
    MeasurableEmbedding (lowerTriangularQuotientMap m F) := by
  let := T.topology
  let := borel (lowerTriangularSubgroup m F)
  have : BorelSpace (lowerTriangularSubgroup m F) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent m F))
  have : BorelSpace (LeftQuotient (upperUnipotent m F)) := ⟨rfl⟩
  exact (isOpenEmbedding_lowerTriangularQuotientMap T m).measurableEmbedding

/-- Pullback of a right-invariant quotient measure, finite on compacts, to the
lower triangular group: it is right invariant and finite on compacts, and when
the cell is conull its pushforward is the quotient measure. -/
theorem comap_lowerTriangularQuotientMap_properties (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    letI := borel (lowerTriangularSubgroup m F)
    letI := borel (LeftQuotient (upperUnipotent m F))
    ∀ (μ : Measure (LeftQuotient (upperUnipotent m F))),
      IsFiniteMeasureOnCompacts μ →
      (∀ g, MeasurePreserving (rightTranslate (upperUnipotent m F) g) μ μ) →
      let ρ := μ.comap (lowerTriangularQuotientMap m F)
      ρ.IsMulRightInvariant ∧ IsFiniteMeasureOnCompacts ρ ∧
        (μ (range (lowerTriangularQuotientMap m F))ᶜ = 0 →
          ρ.map (lowerTriangularQuotientMap m F) = μ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  let := borel (lowerTriangularSubgroup m F)
  have : BorelSpace (lowerTriangularSubgroup m F) := ⟨rfl⟩
  let := borel (LeftQuotient (upperUnipotent m F))
  have : BorelSpace (LeftQuotient (upperUnipotent m F)) := ⟨rfl⟩
  intro μ hμ hinv ρ
  have hβ := lowerTriangularQuotientMap_measurableEmbedding (F := F) T m
  have hβc : Continuous (lowerTriangularQuotientMap m F) :=
    (isOpenEmbedding_lowerTriangularQuotientMap T m).continuous
  refine ⟨⟨fun c => ?_⟩, ⟨fun K hK => ?_⟩, fun hnull => ?_⟩
  · ext S hS
    rw [Measure.map_apply (measurable_mul_const c) hS, hβ.comap_apply, hβ.comap_apply]
    have himage : lowerTriangularQuotientMap m F '' ((fun x => x * c) ⁻¹' S) =
        rightTranslate (upperUnipotent m F) c.val ⁻¹'
          (lowerTriangularQuotientMap m F '' S) := by
      ext q
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b * c, hb, lowerTriangularQuotientMap_mul T m b c⟩
      · rintro ⟨b, hb, hq⟩
        refine ⟨b * c⁻¹, by simpa using hb, ?_⟩
        have := congrArg (rightTranslate (upperUnipotent m F) c⁻¹.val) hq
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

end Langlands.AllField.RankinSelberg
