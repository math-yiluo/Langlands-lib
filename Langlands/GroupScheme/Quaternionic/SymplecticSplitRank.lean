import Langlands.GroupScheme.FiniteAlgebraWeightedNontrivial
import Langlands.GroupScheme.Quaternionic.SymplecticCocharacter
import Langlands.GroupScheme.Quaternionic.HyperbolicBasis
import Langlands.GroupScheme.Quaternionic.RankOneCriterion

/-! # Split rank one for antihermitian forms of rank two or three -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.WeightedRoot

variable {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D)

section Cocharacters

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The pair-weight cocharacter of a supported form is nonzero when the two
distinguished coordinates are distinct. -/
theorem symplecticCocharacter_ne_zero (H : Matrix n n D) (a b : n) (hab : a ≠ b)
    (hH : ∀ i j, H i j ≠ 0 → pairWeight a b i + pairWeight a b j = 0) :
    σ.symplecticCocharacter H a b hH ≠ 0 := by
  intro hz
  have hne := cocharacter_ne_zero_of_weight_eq_one K D
    (Module.finBasis K (Matrix n n D)) (pairWeight a b) a
    (by simp [pairWeight, hab])
  apply hne
  change ambientCocharacter K D (pairWeight a b) = 0
  rw [← σ.symplecticCocharacter_comp H a b hH, hz, Limits.zero_comp]

end Cocharacters

/-- The standard hyperbolic plane has a nontrivial actual cocharacter. -/
theorem hasNontrivialCocharacter_gramTwo :
    HasNontrivialCocharacter (σ.symplecticGroup (gramTwo D)) := by
  have hH : ∀ i j, gramTwo D i j ≠ 0 →
      pairWeight (0 : Fin 2) 1 i + pairWeight (0 : Fin 2) 1 j = 0 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [gramTwo, pairWeight]
  exact ⟨σ.symplecticCocharacter (gramTwo D) 0 1 hH,
    σ.symplecticCocharacter_ne_zero (gramTwo D) 0 1 (by decide) hH⟩

/-- A hyperbolic plane with one orthogonal coordinate has a nontrivial
actual cocharacter, independently of the value of that coordinate. -/
theorem hasNontrivialCocharacter_gramThree (c : D) :
    HasNontrivialCocharacter (σ.symplecticGroup (gramThree c)) := by
  have hH : ∀ i j, gramThree c i j ≠ 0 →
      pairWeight (0 : Fin 3) 1 i + pairWeight (0 : Fin 3) 1 j = 0 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [gramThree, pairWeight]
  exact ⟨σ.symplecticCocharacter (gramThree c) 0 1 hH,
    σ.symplecticCocharacter_ne_zero (gramThree c) 0 1 (by decide) hH⟩

omit [Infinite K] in
private theorem hasNontrivialCocharacter_of_iso
    {G G' : GroupScheme (Spec (CommRingCat.of K))} (e : G ≅ G')
    (h : HasNontrivialCocharacter G') : HasNontrivialCocharacter G := by
  obtain ⟨χ, hχ⟩ := h
  refine ⟨χ ≫ e.inv, ?_⟩
  intro hz
  apply hχ
  have he := congrArg (fun f => f ≫ e.hom) hz
  simpa only [Category.assoc, e.inv_hom_id, Category.comp_id, Limits.zero_comp] using he

/-- A nondegenerate trace-valued antihermitian form of rank two or three and
Witt index one has a nontrivial cocharacter of its reduced-norm-one isometry group. -/
theorem hasNontrivialCocharacter_of_wittIndex_eq_one
    {m : ℕ} [NeZero m] (hm : m = 2 ∨ m = 3)
    (H : Matrix (Fin m) (Fin m) D) (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    (hw : σ.wittIndex H = 1) :
    HasNontrivialCocharacter (σ.symplecticGroup H) := by
  rcases hm with rfl | rfl
  · obtain ⟨P, hP, hPH⟩ := exists_gramTwo hH hu hw
    have e := σ.symplecticGroupCongr hP.unit H
    rw [IsUnit.unit_spec, hPH] at e
    exact hasNontrivialCocharacter_of_iso e σ.hasNontrivialCocharacter_gramTwo
  · obtain ⟨P, c, _, _, hP, hPH⟩ := exists_gramThree hH hu hw
    have e := σ.symplecticGroupCongr hP.unit H
    rw [IsUnit.unit_spec, hPH] at e
    exact hasNontrivialCocharacter_of_iso e (σ.hasNontrivialCocharacter_gramThree c)

/-- The actual symplectic group has split rank one for these forms, over any
infinite field and without a characteristic or quaternion-dimension hypothesis. -/
theorem splitRank_symplecticGroup_eq_one_of_wittIndex_eq_one
    {m : ℕ} [NeZero m] (hm : m = 2 ∨ m = 3)
    (H : Matrix (Fin m) (Fin m) D) (hH : σ.IsAntihermitian H) (hu : IsUnit H)
    (hw : σ.wittIndex H = 1) :
    splitRank (σ.symplecticGroup H) = 1 :=
  σ.splitRank_symplecticGroup_eq_one_of_nontrivialCocharacter H hw.le
    (σ.hasNontrivialCocharacter_of_wittIndex_eq_one hm H hH hu hw)

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
