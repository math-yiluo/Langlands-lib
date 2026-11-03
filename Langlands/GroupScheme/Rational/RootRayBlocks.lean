import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Actual-root blocks for ordered semigroup products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual relative roots on the positive integral ray through `a`.
Characters on the ray which are not roots are omitted. -/
def rootRayBlock (i : S.toGrp ⟶ G) (a : characterLattice S) :
    Set (characterLattice S) :=
  relativeRoots i ∩ (cyclicTail a 1 : Set (characterLattice S))

@[simp] theorem mem_rootRayBlock (i : S.toGrp ⟶ G) (a χ : characterLattice S) :
    χ ∈ rootRayBlock i a ↔ χ ∈ relativeRoots i ∧ χ ∈ cyclicTail a 1 :=
  Iff.rfl

/-- The initial character belongs to its first positive cyclic tail. -/
theorem self_mem_cyclicTail_one (a : characterLattice S) : a ∈ cyclicTail a 1 :=
  ⟨1, le_rfl, Nat.zero_lt_one, one_nsmul a⟩

/-- An actual root belongs to its own root-ray block. -/
theorem self_mem_rootRayBlock (i : S.toGrp ⟶ G) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) : a ∈ rootRayBlock i a :=
  ⟨ha, self_mem_cyclicTail_one a⟩

/-- Positive integral multiples of an element in an additive semigroup remain
in that semigroup; zero is not inserted. -/
private theorem positive_nsmul_mem (A : AddSubsemigroup (characterLattice S))
    {a : characterLattice S} (ha : a ∈ A) (m : ℕ) (hm : 0 < m) : m • a ∈ A := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simpa using ha
      · simpa only [succ_nsmul] using A.add_mem (ih (by omega)) ha

/-- The actual roots in a ray generate the entire positive cyclic semigroup,
provided the initial character is an actual root. -/
theorem closure_rootRayBlock (i : S.toGrp ⟶ G) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) :
    AddSubsemigroup.closure (rootRayBlock i a) = cyclicTail a 1 := by
  apply le_antisymm
  · exact AddSubsemigroup.closure_le.mpr (fun _ hχ => hχ.2)
  · rintro χ ⟨m, _, hm, rfl⟩
    exact positive_nsmul_mem _
      (AddSubsemigroup.subset_closure (self_mem_rootRayBlock i ha)) m hm

/-- A positive cyclic ray stays in the strict positive pairing halfspace. -/
theorem cyclicTail_one_le_positiveSemigroup {a : characterLattice S}
    {ν : cocharacterLattice S} (ha : 0 < latticePairing S a ν) :
    cyclicTail a 1 ≤ positiveSemigroup ν := by
  rintro χ ⟨m, _, hm, rfl⟩
  exact positive_nsmul_mem (positiveSemigroup ν) ha m hm

/-- Each block indexed by an indivisible positive actual root consists of
positive actual roots. -/
theorem rootRayBlock_subset_positiveRelativeRoots (i : S.toGrp ⟶ G)
    {ν : cocharacterLattice S} {a : characterLattice S}
    (ha : a ∈ indivisiblePositiveRoots i ν) :
    rootRayBlock i a ⊆ positiveRelativeRoots i ν := by
  intro χ hχ
  exact ⟨hχ.1, cyclicTail_one_le_positiveSemigroup ha.2 hχ.2⟩

/-- Reindexing the published ray cover by any enumeration of its indexing set
covers precisely the actual positive roots. -/
theorem iUnion_rootRayBlock (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    (hcover : ∀ χ ∈ relativeRoots i, 0 < latticePairing S χ ν ↔
      ∃ b ∈ indivisiblePositiveRoots i ν, χ ∈ cyclicTail b 1) :
    (⋃ r, rootRayBlock i (a r)) = positiveRelativeRoots i ν := by
  ext χ
  constructor
  · intro hχ
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hχ
    exact rootRayBlock_subset_positiveRelativeRoots i
      (ha ▸ Set.mem_range_self r) hr
  · intro hχ
    obtain ⟨b, hb, hχb⟩ := (hcover χ hχ.1).mp hχ.2
    obtain ⟨r, rfl⟩ := ha.symm ▸ hb
    exact Set.mem_iUnion.mpr ⟨r, hχ.1, hχb⟩

/-- Disjoint positive rays give the exact block disjointness and cross-exclusion
required by the semigroup ordered-product theorem. -/
theorem rootRayBlock_pairwise (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hinj : Function.Injective a)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    (hdisj : ∀ b ∈ indivisiblePositiveRoots i ν,
      ∀ c ∈ indivisiblePositiveRoots i ν, b ≠ c →
        Disjoint (cyclicTail b 1 : Set (characterLattice S))
          (cyclicTail c 1 : Set (characterLattice S))) :
    (∀ r q : Fin n, r ≠ q → Disjoint (rootRayBlock i (a r)) (rootRayBlock i (a q))) ∧
    (∀ r q : Fin n, r ≠ q → Disjoint (rootRayBlock i (a r))
      (AddSubsemigroup.closure (rootRayBlock i (a q)) : Set (characterLattice S))) := by
  have hmem (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have htail (r q : Fin n) (hrq : r ≠ q) :
      Disjoint (cyclicTail (a r) 1 : Set (characterLattice S))
        (cyclicTail (a q) 1 : Set (characterLattice S)) :=
    hdisj _ (hmem r) _ (hmem q) (fun h => hrq (hinj h))
  constructor
  · intro r q hrq
    exact (htail r q hrq).mono (fun _ h => h.2) (fun _ h => h.2)
  · intro r q hrq
    rw [closure_rootRayBlock i (hmem q).1.1]
    exact (htail r q hrq).mono_left (fun _ h => h.2)

end Langlands.GroupScheme.RelativeRoot
