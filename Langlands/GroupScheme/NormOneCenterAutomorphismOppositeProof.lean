import Langlands.GroupScheme.NormOneCenterAutomorphismOppositeStatement
import Langlands.GroupScheme.NormOneSplittingAffine

/-! # Centre-moving norm-one automorphisms force an opposite-algebra equivalence -/

noncomputable section

universe u

namespace Langlands.GroupScheme

open Langlands.CentralSimple

/-- A centre-moving automorphism of the actual reduced-norm-one group scheme of
a central simple algebra forces a scalar-fixing equivalence with its opposite. -/
theorem normOneCenterAutomorphismOpposite : NormOneCenterAutomorphismOppositeStatement.{u} := by
  intro K A _ _ _ _ _ _ f hf
  let L := finiteGaloisSplittingField K A
  let e := finiteGaloisSplittingChart K A
  obtain ⟨H, hH⟩ := CentralSimpleUnits.Splitting.exists_coefficient_outer_matrix K A e f hf
  exact ⟨NormOneOuterDescent.oppositeEquivOfOuter K A L e
    (CentralSimpleUnits.coefficientAutomorphism K A f
      (CommAlgCat.of (CommRingCat.of K) L)) H hH
    (fun σ x => CentralSimpleUnits.coefficientAutomorphism_covariant K A L f σ x)⟩

end Langlands.GroupScheme
