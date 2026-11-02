import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationFirstLevelCharts

/-! # Empty tails and descending first-level induction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- An empty relation object already gives an affine finite type first level. -/
def affineFiniteTypeFirstLevel_of_isEmpty (E : EtaleEquivalenceRelation.{u})
    [IsEmpty E.U] : AffineFiniteTypeFirstLevel E := by
  let : IsEmpty E.R := Function.isEmpty E.s
  exact
    { relation := E
      comparison := 𝟙 E
      object_isAffine := inferInstance
      object_finiteType := inferInstance
      arrows_isAffine := inferInstance }

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

/-- The tail beyond the last selected length has no object points. -/
lemma tupleTailPresentation_object_isEmpty (N : ℕ) :
    IsEmpty (E.tupleTailPresentation N (N + 1)).U := by
  let : IsEmpty {i : Fin (N + 1) // N + 1 ≤ i.val} :=
    ⟨fun i => (Nat.not_lt_of_ge i.property) i.val.isLt⟩
  change IsEmpty ((∐ fun i : {i : Fin (N + 1) // N + 1 ≤ i.val} =>
    E.tupleSymmetricScheme i.val.val) : Scheme.{u})
  refine ⟨fun x => ?_⟩
  let i : {i : Fin (N + 1) // N + 1 ≤ i.val} := (sigmaOpenCover _).idx x
  exact (Nat.not_lt_of_ge i.property) i.val.isLt

/-- The last, empty tail is the base case of descending induction. -/
def tupleTailEmptyFirstLevel (N : ℕ) :
    AffineFiniteTypeFirstLevel (E.tupleTailPresentation N (N + 1)) := by
  let := E.tupleTailPresentation_object_isEmpty N
  exact affineFiniteTypeFirstLevel_of_isEmpty _

/-- Supplied systems on the actual next-threshold restrictions close the
descending induction and give a first level of the original relation. -/
lemma nonempty_affineFiniteTypeFirstLevel_of_tupleTail_systems (N : ℕ)
    (step : ∀ (p : ℕ), p < N + 1 →
      AffineFiniteTypeFirstLevel (E.tupleTailPresentation N (p + 1)) →
        Nonempty (FiniteTypeCartesianSystem (E.tupleTailNextRelation N p))) :
    Nonempty (AffineFiniteTypeFirstLevel E) := by
  have h : Nonempty (AffineFiniteTypeFirstLevel (E.tupleTailPresentation N 0)) := by
    apply Nat.decreasingInduction (motive := fun p _ =>
      Nonempty (AffineFiniteTypeFirstLevel (E.tupleTailPresentation N p)))
      (n := N + 1) ?_ ⟨E.tupleTailEmptyFirstLevel N⟩ (Nat.zero_le _)
    intro p hp ih
    obtain ⟨M⟩ := ih
    obtain ⟨D⟩ := step p hp M
    exact E.nonempty_affineFiniteTypeFirstLevel_tupleTail N p hp D
  obtain ⟨M⟩ := h
  exact E.nonempty_affineFiniteTypeFirstLevel_of_tupleTail_zero N M

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
