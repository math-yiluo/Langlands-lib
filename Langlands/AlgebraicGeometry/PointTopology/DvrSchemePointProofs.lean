import Langlands.AlgebraicGeometry.PointTopology.DvrSchemePointStatements
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs
import Mathlib.Topology.Algebra.Valued.ValuedField

/-! # Continuity, openness and separated injectivity of actual DVR points -/

noncomputable section
universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped WithZero

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

theorem dvrSchemePointProperties_proof : DvrSchemePointProperties R K := by
  let : Valued K ℤᵐ⁰ := Valued.mk' ((IsDiscreteValuationRing.maximalIdeal R).valuation K)
  let : TopologicalSpace R := TopologicalSpace.induced (algebraMap R K) inferInstance
  have hi : IsInducing (algebraMap R K) := ⟨rfl⟩
  let : IsTopologicalRing R := {
    continuous_add := by
      apply hi.continuous_iff.mpr
      simpa only [Function.comp_def, map_add] using
        continuous_add.comp₂ (hi.continuous.comp continuous_fst)
          (hi.continuous.comp continuous_snd)
    continuous_mul := by
      apply hi.continuous_iff.mpr
      simpa only [Function.comp_def, map_mul] using
        continuous_mul.comp₂ (hi.continuous.comp continuous_fst)
          (hi.continuous.comp continuous_snd)
    continuous_neg := by
      apply hi.continuous_iff.mpr
      simpa only [Function.comp_def, map_neg] using continuous_neg.comp hi.continuous }
  have he : IsEmbedding (algebraMap R K) :=
    ⟨hi, IsFractionRing.injective R K⟩
  have hr : Set.range (algebraMap R K) =
      (((IsDiscreteValuationRing.maximalIdeal R).valuation K).valuationSubring : Set K) := by
    ext x
    change (∃ a, algebraMap R K a = x) ↔
      ((IsDiscreteValuationRing.maximalIdeal R).valuation K) x ≤ 1
    constructor
    · rintro ⟨a, rfl⟩
      exact (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one a
    · exact IsDiscreteValuationRing.exists_lift_of_le_one
  have ho : IsOpenEmbedding (Algebra.ofId R K) := by
    refine ⟨he, ?_⟩
    change IsOpen (Set.range (algebraMap R K))
    rw [hr]
    exact Valued.isOpen_valuationSubring K
  intro X _
  let : TopologicalSpace (RingPoint R X R) := schemePointTopology R X R
  let : TopologicalSpace (RingPoint R X K) := schemePointTopology R X K
  let : TopologicalSpace (RingPoint K (ringBaseChange R K X) K) :=
    schemePointTopology K (ringBaseChange R K X) K
  let g := RingPoint.changeRing (X := X) (Algebra.ofId R K)
  let b := ringPointBaseChangeEquiv R K K X
  have hg : Continuous g := schemeCoefficientContinuity_proof R R K X _ ho.continuous
  have hgo : IsOpenMap g := schemeCoefficientOpen_proof R R K X _ ho
  have hb : IsHomeomorph b := schemeBaseChangeTopology_proof R K K X
  have hc : Continuous (b ∘ g) := hb.continuous.comp hg
  have hOpen : IsOpenMap (b ∘ g) := hb.isOpenMap.comp hgo
  refine ⟨hc, hOpen, ?_⟩
  intro _
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap hc _ hOpen
  exact b.injective.comp
    (schemeSeparatedCoefficientInjectivity_proof R R K X _ ho.injective)

end Langlands.AlgebraicGeometry.PointTopology
