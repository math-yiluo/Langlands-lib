import Langlands.Representation.Compact.CompactFiniteTypeAdmissibleProof
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.CompactCoefficient.Subquotients
import Langlands.Representation.Smooth.Schur.Proof

/-! # A nonzero compact representation forces a compact center -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

open MeasureTheory TopologicalSpace

/-- Renard IV.1.3, Lemma, for the exact published nonzero compact representation target. -/
theorem compactRepresentationCompactCenter :
    CompactRepresentationCompactCenterStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ π hnonzero hc
  let := hnonzero
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  have hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hL, hLK⟩
  obtain ⟨σ, hσ, hσπ⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial π
  have hcompact := SmoothRep.hasCompactSmoothDualCoefficients_of_isSubquotient hcof hc hσπ
  have ha := CompactSplitting.isAdmissible_of_compactCoefficients
    μ hcof σ.representation σ.isSmooth hσ hcompact
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ := admissibleSchur_centralCharacter σ.representation ha hσ
  let : σ.representation.IsIrreducible := hσ
  let : Nontrivial σ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.representation.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : σ)
  obtain ⟨ℓ, hℓ, _, hℓx⟩ := CompactCoefficientSemisimplicity.exists_smooth_dual_separating
    σ.representation σ.isSmooth ⊥ (by change x ∉ (⊥ : Submodule ℂ σ); simpa only [Submodule.mem_bot] using hx)
  have hsupp : (Subgroup.center G : Set G) ⊆ tsupport (matrixCoefficient σ.representation ℓ x) := by
    intro z hz
    apply subset_tsupport
    change ℓ (σ.representation z x) ≠ 0
    rw [hχ ⟨z, hz⟩, map_smul]
    exact mul_ne_zero (χ ⟨z, hz⟩).ne_zero hℓx
  have hclosed : IsClosed (Subgroup.center G : Set G) := by
    have heq : (Subgroup.center G : Set G) = ⋂ g : G, {z | g * z = z * g} := by
      ext z
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact Subgroup.mem_center_iff
    rw [heq]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id)
      (continuous_id.mul continuous_const)
  exact (hcompact x ℓ hℓ).isCompact.of_isClosed_subset hclosed hsupp

/-- Renard IV.1.3: the exact coefficient criterion, finite-type admissibility and compact-center conjunction. -/
theorem compactRepresentationCriterionStatements : CompactRepresentationCriterionStatements.{u, v} :=
  ⟨compactRepresentationCoefficientCriterion, compactFiniteTypeAdmissible,
    compactRepresentationCompactCenter⟩

end Langlands.Renard.CompactRepresentation
