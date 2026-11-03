import Langlands.GroupScheme.Rational.ActionWeightComparisonProof

/-! # Actual roots and ambient action-weight sign support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The full adjoint weight support, including the zero character when its
weight space is nonzero. -/
def adjointWeightSupport (i : S.toGrp ⟶ G) : Set (characterLattice S) :=
  {χ | weightSpace i χ ≠ ⊥}

theorem mem_adjointWeightSupport (i : S.toGrp ⟶ G) (χ : characterLattice S) :
    χ ∈ adjointWeightSupport i ↔ weightSpace i χ ≠ ⊥ := Iff.rfl

/-- Ambient conjugation support consists of the nonzero adjoint weight spaces,
including the zero character when its weight space is nonzero. -/
theorem mem_actionWeightSupport_conjugation_top (i : S.toGrp ⟶ G)
    (χ : characterLattice S) :
    χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤ ↔
      weightSpace i χ ≠ ⊥ := by
  rw [← actionWeightSpace_conjugation i χ]
  constructor
  · rintro ⟨X, hX, hmem, _⟩
    exact (Submodule.ne_bot_iff _).mpr ⟨X, hmem, hX⟩
  · intro h
    obtain ⟨X, hmem, hX⟩ := (Submodule.ne_bot_iff _).mp h
    exact ⟨X, hX, hmem, Subgroup.mem_top _⟩

/-- The full adjoint weight support is the ambient conjugation-action support. -/
theorem adjointWeightSupport_eq_actionWeightSupport_conjugation_top
    (i : S.toGrp ⟶ G) :
    adjointWeightSupport i =
      actionWeightSupport (AutomorphicAction.conjugation i) ⊤ := by
  ext χ
  exact (mem_actionWeightSupport_conjugation_top i χ).symm

/-- Actual relative roots are the nonzero characters in the adjoint support. -/
theorem mem_relativeRoots_iff_adjointWeightSupport
    (i : S.toGrp ⟶ G) (χ : characterLattice S) :
    χ ∈ relativeRoots i ↔ χ ≠ 0 ∧ χ ∈ adjointWeightSupport i := by
  rw [mem_relativeRoots, mem_adjointWeightSupport]

/-- Actual relative roots are exactly the nonzero ambient action weights. -/
theorem mem_relativeRoots_iff_actionWeightSupport_conjugation_top
    (i : S.toGrp ⟶ G) (χ : characterLattice S) :
    χ ∈ relativeRoots i ↔
      χ ≠ 0 ∧ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤ := by
  rw [mem_relativeRoots_iff_adjointWeightSupport,
    adjointWeightSupport_eq_actionWeightSupport_conjugation_top]

/-- The ambient support differs from the actual root set only at zero. -/
theorem relativeRoots_eq_actionWeightSupport_conjugation_top_diff_zero
    (i : S.toGrp ⟶ G) :
    relativeRoots i =
      actionWeightSupport (AutomorphicAction.conjugation i) ⊤ \ {0} := by
  ext χ
  rw [mem_relativeRoots_iff_actionWeightSupport_conjugation_top,
    Set.mem_sdiff, Set.mem_singleton_iff]
  exact and_comm

/-- A support implication on actual roots extends to the ambient support
whenever its zero-character case is already known. -/
theorem rootSupport_imp_iff_actionWeightSupport_imp (i : S.toGrp ⟶ G)
    (P Q : characterLattice S → Prop) (hzero : P 0 → Q 0) :
    (∀ χ ∈ relativeRoots i, P χ → Q χ) ↔
      ∀ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤, P χ → Q χ := by
  constructor
  · intro h χ hχ hP
    by_cases hχ0 : χ = 0
    · subst χ
      exact hzero hP
    · exact h χ
        ((mem_relativeRoots_iff_actionWeightSupport_conjugation_top i χ).mpr
          ⟨hχ0, hχ⟩) hP
  · intro h χ hχ
    exact h χ
      ((mem_relativeRoots_iff_actionWeightSupport_conjugation_top i χ).mp hχ).2

/-- Rootwise nonnegative sign containment is semigroup containment restricted
to the ambient conjugation-action support. -/
theorem nonnegative_rootSupport_iff (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    (∀ χ ∈ relativeRoots i,
      0 ≤ latticePairing S χ zeta → 0 ≤ latticePairing S χ eta) ↔
    ∀ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤,
      χ ∈ nonnegativeSemigroup zeta → χ ∈ nonnegativeSemigroup eta := by
  apply rootSupport_imp_iff_actionWeightSupport_imp i
    (fun χ => 0 ≤ latticePairing S χ zeta)
    (fun χ => 0 ≤ latticePairing S χ eta)
  intro _
  simp

/-- Rootwise positive sign containment is semigroup containment restricted
to the ambient conjugation-action support. -/
theorem positive_rootSupport_iff (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    (∀ χ ∈ relativeRoots i,
      0 < latticePairing S χ zeta → 0 < latticePairing S χ eta) ↔
    ∀ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) ⊤,
      χ ∈ positiveSemigroup zeta → χ ∈ positiveSemigroup eta := by
  apply rootSupport_imp_iff_actionWeightSupport_imp i
    (fun χ => 0 < latticePairing S χ zeta)
    (fun χ => 0 < latticePairing S χ eta)
  simp

/-- Set-theoretic form of the nonnegative root-support comparison. -/
theorem nonnegative_rootSupport_iff_inter_subset (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    (∀ χ ∈ relativeRoots i,
      0 ≤ latticePairing S χ zeta → 0 ≤ latticePairing S χ eta) ↔
    actionWeightSupport (AutomorphicAction.conjugation i) ⊤ ∩
      (nonnegativeSemigroup zeta : Set (characterLattice S)) ⊆
        (nonnegativeSemigroup eta : Set (characterLattice S)) := by
  rw [nonnegative_rootSupport_iff i zeta eta]
  exact ⟨fun h χ hχ => h χ hχ.1 hχ.2, fun h χ hχ hz => h ⟨hχ, hz⟩⟩

/-- Set-theoretic form of the positive root-support comparison. -/
theorem positive_rootSupport_iff_inter_subset (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) :
    (∀ χ ∈ relativeRoots i,
      0 < latticePairing S χ zeta → 0 < latticePairing S χ eta) ↔
    actionWeightSupport (AutomorphicAction.conjugation i) ⊤ ∩
      (positiveSemigroup zeta : Set (characterLattice S)) ⊆
        (positiveSemigroup eta : Set (characterLattice S)) := by
  rw [positive_rootSupport_iff i zeta eta]
  exact ⟨fun h χ hχ => h χ hχ.1 hχ.2, fun h χ hχ hz => h ⟨hχ, hz⟩⟩

end Langlands.GroupScheme.RelativeRoot
