import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.LocalGroupIsoOverlap

/-! # Constructing inner discrepancy cocycles from a universal overlap equation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}
  (e : LocalGroupIso G H U) (a : AutomorphicAction A G)

/-- A universal overlap equation supplies the inner discrepancy on every refinement. -/
theorem hasInnerDiscrepancy_of_overlap {δ : U ⊗ U ⟶ A.X}
    (hδ : e.HasOverlapDiscrepancy a δ) : e.HasInnerDiscrepancy a := by
  intro T b c
  exact ⟨lift b c ≫ δ, fun t g =>
    e.discrepancy_on_refinements_of_overlap a hδ b c t g⟩

/-- All-test innerness is equivalent to one equation on the actual universal overlap. -/
theorem hasInnerDiscrepancy_iff_overlap :
    e.HasInnerDiscrepancy a ↔ ∃ δ : U ⊗ U ⟶ A.X, e.HasOverlapDiscrepancy a δ := by
  constructor
  · intro he
    obtain ⟨δ, hδ⟩ := he (fst U U) (snd U U)
    exact ⟨δ, hδ (fst (U ⊗ U) G.X) (snd (U ⊗ U) G.X)⟩
  · rintro ⟨δ, hδ⟩
    exact e.hasInnerDiscrepancy_of_overlap a hδ

variable (ha : a.IsFaithful) {δ : U ⊗ U ⟶ A.X}
  (hδ : e.HasOverlapDiscrepancy a δ)

/-- Faithfulness constructs a natural cocycle from the single universal equation. -/
def overlapCocycle : Cocycle A U :=
  e.innerCocycle a ha (e.hasInnerDiscrepancy_of_overlap a hδ)

/-- The constructed cocycle has the original discrepancy on every relative test. -/
theorem overlapCocycle_hasDiscrepancy :
    e.HasDiscrepancy a (e.overlapCocycle a ha hδ) :=
  e.innerCocycle_hasDiscrepancy a ha (e.hasInnerDiscrepancy_of_overlap a hδ)

/-- Its universal overlap value is precisely the supplied actual morphism. -/
@[simp] theorem overlapCocycle_overlap : (e.overlapCocycle a ha hδ).overlap = δ := by
  apply RepresentsDiscrepancy.unique e a ha (b := fst U U) (c := snd U U)
  · intro W t g
    rw [Cocycle.overlap, ← (e.overlapCocycle a ha hδ).naturality]
    exact e.overlapCocycle_hasDiscrepancy a ha hδ (t ≫ fst U U) (t ≫ snd U U) g
  · intro W t g
    simpa only [← comp_lift, lift_fst_snd, Category.comp_id] using
      e.discrepancy_of_overlap a hδ (t ≫ fst U U) (t ≫ snd U U) g

/-- The universal equation determines a unique natural discrepancy cocycle. -/
theorem overlapCocycle_unique (ξ : Cocycle A U) (hξ : e.HasDiscrepancy a ξ) :
    ξ = e.overlapCocycle a ha hδ :=
  e.innerCocycle_unique a ha (e.hasInnerDiscrepancy_of_overlap a hδ) ξ hξ

end Langlands.GroupScheme.LocalGroupIso
