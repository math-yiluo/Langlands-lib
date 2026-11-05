import Langlands.Global.InfiniteCompletionRCLike
import Langlands.GroupScheme.Dynamic.LeviCompatiblePolarIwasawa

/-! # Actual archimedean Levi-compatible Iwasawa assembly from realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.InfinitePlaceGroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Compatible diagonal star realization on the actual completion pullback,
using an analytic structure with the original completion norm and topology. -/
def HasCompletionDiagonalStarLeviRealization
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (v : NumberField.InfinitePlace F) : Prop := by
  letI : IsRCLikeNormedField v.Completion := v.completion_isRCLikeNormedField
  letI := IsRCLikeNormedField.rclike v.Completion
  exact Dynamic.HasDiagonalStarLeviRealization
    ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p)
    ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map l ≫
      (GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p)

/-- Realization on the completion pullback supplies all four conclusions on
the original point groups with their existing evaluation topologies. -/
theorem exists_leviCompatibleIwasawaCompact_of_completion_realization
    (hG : IsConnectedReductive G)
    (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G)
    (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P)
    (hl : IsRationalLeviSubgroup l) (v : NumberField.InfinitePlace F)
    (h : HasCompletionDiagonalStarLeviRealization F G P p M l v) :
    ∃ K, IsLeviCompatibleIwasawaCompact F G P p M l v K := by
  let : IsRCLikeNormedField v.Completion := v.completion_isRCLikeNormedField
  let := IsRCLikeNormedField.rclike v.Completion
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom M.X.hom := hl.isConnectedReductive.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have hr : Dynamic.HasDiagonalStarLeviRealization
      ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p)
      ((GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map l ≫
        (GroupScheme.baseChange (Spec.algebraMap F v.Completion)).map p) := h
  exact (hasLeviCompatibleDecomposition_completionBaseChange_iff F G P p M l v).mpr
    hr.hasLeviCompatibleDecomposition

/-- The remaining compatible realization obligation, quantified over exactly
the rational pairs and infinite places of the published Iwasawa target. -/
def CompletionDiagonalStarLeviRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G),
      IsParabolicSubgroup p →
      ∀ (M : GroupScheme (Spec (CommRingCat.of F))) (l : M ⟶ P),
        IsRationalLeviSubgroup l →
        ∀ v : NumberField.InfinitePlace F,
          HasCompletionDiagonalStarLeviRealization F G P p M l v

/-- Conditional assembly of the exact existing universe-polymorphic target.
The realization statement is retained as an unproved hypothesis. -/
theorem leviCompatibleIwasawaStatement_of_completion_realization
    (h : CompletionDiagonalStarLeviRealizationStatement.{u}) :
    LeviCompatibleIwasawaStatement.{u} := by
  intro F _ _ G hG P p hp M l hl v
  exact exists_leviCompatibleIwasawaCompact_of_completion_realization F G hG P p M l hl v
    (h F G hG P p hp M l hl v)

end Langlands.Global.InfinitePlaceGroupPoints
