import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Semigroup action support and positive relative-root indexing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- For the whole group, support means precisely a nonzero action weight space.
The character itself is permitted to be zero. -/
theorem actionWeightSupport_top (b : AutomorphicAction S.toGrp G) :
    actionWeightSupport b ⊤ = {χ | actionWeightSpace b χ ≠ ⊥} := by
  ext χ
  constructor
  · rintro ⟨X, hX0, hXχ, _⟩
    exact (Submodule.ne_bot_iff _).mpr ⟨X, hXχ, hX0⟩
  · intro hχ
    obtain ⟨X, hXχ, hX0⟩ := (Submodule.ne_bot_iff _).mp hχ
    exact ⟨X, hX0, hXχ, Subgroup.mem_top _⟩

/-- An exact semigroup Lie image and the support bound determine the support.
No independence theorem for distinct eigenspaces is needed. -/
theorem actionWeightSupport_eq_inter_of_hasLieImage
    (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (F : SubgroupFunctor G)
    (hLie : HasLieImage F (semigroupWeightSpan b A))
    (hA : actionWeightSupport b F ⊆ A) :
    actionWeightSupport b F = actionWeightSupport b ⊤ ∩ (A : Set _) := by
  ext χ
  constructor
  · intro hχ
    exact ⟨actionWeightSupport_mono b (fun _ _ _ => Subgroup.mem_top _) hχ, hA hχ⟩
  · rintro ⟨⟨X, hX0, hXχ, _⟩, hχA⟩
    refine ⟨X, hX0, hXχ, (hLie X).mpr ?_⟩
    exact (le_iSup_of_le ⟨χ, hχA⟩ le_rfl :
      actionWeightSpace b χ ≤ semigroupWeightSpan b A) hXχ

/-- The realization statement's Lie image and maximality clauses identify the
complete support of its actual generated subgroup. -/
theorem actionWeightSupport_semigroupSubgroup
    (hReal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) :
    actionWeightSupport b (semigroupSubgroup b A) =
      actionWeightSupport b ⊤ ∩ (A : Set _) := by
  obtain ⟨hClosed, hStable, hLie, _, hMax, _⟩ :=
    hReal k G hG inferInstance S hS b A
  exact actionWeightSupport_eq_inter_of_hasLieImage b A _ hLie
    ((hMax _ hClosed hStable).mpr le_rfl)

/-- Strictly positive conjugation weights of the whole group are exactly its
actual positive relative roots. Positivity excludes the zero character. -/
theorem actionWeightSupport_top_inter_positiveSemigroup
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    actionWeightSupport (AutomorphicAction.conjugation i) ⊤ ∩
      (positiveSemigroup ν : Set _) = positiveRelativeRoots i ν := by
  rw [actionWeightSupport_top]
  ext χ
  change (actionWeightSpace (AutomorphicAction.conjugation i) χ ≠ ⊥ ∧
    0 < latticePairing S χ ν) ↔
      (χ ≠ 0 ∧ weightSpace i χ ≠ ⊥) ∧ 0 < latticePairing S χ ν
  rw [actionWeightSpace_conjugation]
  constructor
  · rintro ⟨hχ, hpos⟩
    refine ⟨⟨?_, hχ⟩, hpos⟩
    intro hzero
    subst χ
    simp at hpos
  · rintro ⟨⟨_, hχ⟩, hpos⟩
    exact ⟨hχ, hpos⟩

/-- Conditional on realization, the actual positive semigroup subgroup has
exactly the positive relative roots as its complete action support. -/
theorem actionWeightSupport_positiveSemigroup
    (hReal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    actionWeightSupport (AutomorphicAction.conjugation i)
      (semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν)) =
        positiveRelativeRoots i ν := by
  rw [actionWeightSupport_semigroupSubgroup hReal hG hS,
    actionWeightSupport_top_inter_positiveSemigroup]

/-- The positive actual-root indexing of the realized positive semigroup
support, preserving the underlying character. -/
def positiveSemigroupRootEquiv
    (hReal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    actionWeightSupport (AutomorphicAction.conjugation i)
      (semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν)) ≃
        positiveRelativeRoots i ν :=
  Set.equivOfEq (actionWeightSupport_positiveSemigroup hReal hG hS i ν)

@[simp] theorem positiveSemigroupRootEquiv_val
    (hReal : SemigroupRealizationStatement.{u}) (hG : Smooth G.X.hom)
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (χ : actionWeightSupport (AutomorphicAction.conjugation i)
      (semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν))) :
    (positiveSemigroupRootEquiv hReal hG hS i ν χ).val = χ.val :=
  rfl

end Langlands.GroupScheme.RelativeRoot
