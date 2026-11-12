import Langlands.Representation.Compact.CompactSplittingCriterionStatement
import Langlands.Representation.Compact.CompactSplittingForward
import Langlands.Representation.Compact.CompactSplittingConverse

/-! # Renard IV.1.7: the compact part splits exactly under (KF) -/

namespace Langlands.Renard.CompactRepresentation

universe u v

/-- The exact published compact/noncompact category splitting criterion. -/
theorem compactSplittingCriterion : CompactSplittingCriterionStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ _ μ _ _ _
  dsimp only
  have hbool (P Q : _root_.CategoryTheory.ObjectProperty (SmoothRep.{0, u, v} ℂ G)) :
      (fun b : Bool => if b then P else Q) =
        (fun b : Bool => match b with | false => Q | true => P) := by
    funext b
    cases b <;> rfl
  rw [hbool]
  change Renard.IsCategoryDecomposition
    (SmoothRep.irreducibleSubquotientProperties
      (fun A : SmoothRep.{0, u, v} ℂ G => HasCompactSmoothDualCoefficients A.representation)) ↔
    ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      (CompactCoefficientClass.fixedStratum.{u, v} K.toSubgroup).Finite
  exact ⟨fun h K _ => finite_strata_of_compactCategoryDecomposition h K,
    compactCategoryDecomposition_of_finite_strata μ⟩

end Langlands.Renard.CompactRepresentation
