import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.StandardRootSubsetRange
import Langlands.GroupScheme.Rational.StandardRootSubsetWeyl
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardRootSubsetPairing

/-! # The groups of the standard parabolic root triple -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The generated groups of a standard parabolic root triple are the standard
parabolic, Levi and unipotent groups, with the expected Levi Weyl group. -/
theorem standardParabolicRootSubsetGroup : StandardParabolicRootSubsetGroupStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro R hR ν hν Θ hΘ
  obtain ⟨⟨ζ, hζ⟩, hstd⟩ := standardCocharacter k G hG T i hi ν hν Θ hΘ
  obtain ⟨hP, hM⟩ := StandardRootSubsetPairing.standard_sets_pairing
    hR (relativeRootSystem k G hG T i hi) hi.isSplitSubtorus.1 hν hΘ hζ
  have hN := standardUnipotentRootSubset_eq_of_pairing
    (fun _ ha => StandardRootSubsetPairing.neg_mem hR
      (relativeRootSystem k G hG T i hi) hi.isSplitSubtorus.1 ha) hP
  obtain ⟨hstdP, hstdM, hstdN⟩ := hstd ζ hζ
  refine ⟨?_, ?_, ?_, rootSubsetWeylGroup_standardLevi hG i hi R hR ν hν Θ hΘ⟩
  · intro H h hh
    rw [hstdP]
    rw [hP] at hh
    exact hh.range_eq_dynamicParabolic hG hi hR hν ζ
  · intro H h hh
    rw [hstdM]
    rw [hM] at hh
    exact hh.range_eq_dynamicCentralizer hG hi hR hν ζ
  · intro H h hh
    rw [hstdN]
    rw [hN] at hh
    exact hh.range_eq_dynamicUnipotent hG hi hR hν ζ

end Langlands.GroupScheme
