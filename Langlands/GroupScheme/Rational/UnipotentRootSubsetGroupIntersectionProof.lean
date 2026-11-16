import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.Rational.ClosedRootSubsetAdditiveClosure
import Langlands.GroupScheme.Rational.ClosedRootSubsetSemigroupBound
import Langlands.GroupScheme.Rational.RootSubsetSemigroupComparison
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.SemigroupIntersection

/-! # Borel–Tits 3.22 c): intersection with a unipotent root-generated group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

set_option backward.isDefEq.respectTransparency false

/-- Borel–Tits 3.22 c), in the actual possibly nonreduced relative roots. -/
theorem unipotentRootSubsetGroupIntersection :
    UnipotentRootSubsetGroupIntersectionStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.isSplitSubtorus.mono
  intro ν hν S X hS hX H₁ H₂ H₃ h₁ h₂ h₃ hh₁ hh₂ hh₃
  have hT := hi.isSplitSubtorus.1
  have hE : HasOppositeFactorPairs i := by
    intro a ha x hx hx1
    exact (rootRankOneFactorization k G hG T i hi a ha x hx hx1).1.exists
  let A := AddSubsemigroup.closure X
  let B := (AddSubmonoid.closure S).toAddSubsemigroup
  let b := AutomorphicAction.conjugation i
  have hzero : 0 ∉ A := hX.zero_notMem_addSubsemigroupClosure i
  have hAmonoid : A ≤ (AddSubmonoid.closure X).toAddSubsemigroup :=
    AddSubsemigroup.closure_le.mpr (fun _ hx => AddSubmonoid.subset_closure hx)
  have hrootsX : relativeRoots i ∩ (A : Set (characterLattice T)) = X := by
    ext χ
    constructor
    · rintro ⟨hχ, hχA⟩
      exact hX.1.mem_of_mem_addSubmonoidClosure hG i hi hχ (hAmonoid hχA)
    · intro hχ
      exact ⟨hX.1.1 hχ, AddSubsemigroup.subset_closure hχ⟩
  have hrootsSX :
      relativeRoots i ∩ ((A ⊓ B : AddSubsemigroup _) : Set (characterLattice T)) =
        S ∩ X := by
    ext χ
    constructor
    · rintro ⟨hχ, hχA, hχB⟩
      exact ⟨hS.mem_of_mem_addSubmonoidClosure hG i hi hχ hχB,
        hrootsX ▸ (show χ ∈ relativeRoots i ∩ (A : Set _) from ⟨hχ, hχA⟩)⟩
    · rintro ⟨hχS, hχX⟩
      exact ⟨hX.1.1 hχX, AddSubsemigroup.subset_closure hχX,
        AddSubmonoid.subset_closure hχS⟩
  have h₂eq : SubgroupFunctor.range h₂ = semigroupSubgroup b A :=
    hh₂.range_eq_semigroupSubgroup i hT hE A hzero hrootsX
  have h₃eq : SubgroupFunctor.range h₃ = semigroupSubgroup b (A ⊓ B) :=
    hh₃.range_eq_semigroupSubgroup i hT hE (A ⊓ B)
      (fun hz => hzero hz.1) hrootsSX
  have h₁le : SubgroupFunctor.range h₁ ≤ semigroupSubgroup b B :=
    hh₁.range_le_addSubmonoidSemigroup hG i hi ν hν hS.1
  have h₃le₁ : SubgroupFunctor.range h₃ ≤ SubgroupFunctor.range h₁ :=
    hh₃.range_le_rootSubsetGroup i Set.inter_subset_left hh₁
  have h₃le₂ : SubgroupFunctor.range h₃ ≤ SubgroupFunctor.range h₂ :=
    hh₃.range_le_of_subset i Set.inter_subset_right hh₂
  intro V _ g
  constructor
  · rintro ⟨hg₁, hg₂⟩
    have hg : g ∈ (semigroupSubgroup b A ⊓ semigroupSubgroup b B).carrier V :=
      ⟨h₂eq ▸ hg₂, h₁le V hg₁⟩
    rw [semigroupSubgroup_inf_eq hT b A B hzero, ← h₃eq] at hg
    exact hg
  · intro hg
    exact ⟨h₃le₁ V hg, h₃le₂ V hg⟩

end Langlands.GroupScheme
