import Langlands.GroupScheme.MatrixRepresentation.SplitTorusCharacterDecomposition
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient

/-! # Nonreciprocal weights in faithful split-torus representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

variable {k : Type u} [Field k] {I : Type u} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- A generating subset of a free integer lattice whose nonzero elements are
all equal or opposite can generate only a lattice of rank at most one. -/
theorem card_le_one_of_generators_equal_or_neg {W : Set (I → ℤ)}
    (hW : AddSubgroup.closure W = ⊤)
    (hpair : ∀ m ∈ W, m ≠ 0 → ∀ p ∈ W, p ≠ 0 → p = m ∨ p = -m) :
    Nat.card I ≤ 1 := by
  classical
  have hspan : Submodule.span ℤ W = ⊤ := by
    rw [← AddSubgroup.toIntSubmodule_closure, hW]
    rfl
  suffices hex : ∃ m : I → ℤ, W ⊆ Submodule.span ℤ ({m} : Set (I → ℤ)) by
    obtain ⟨m, hm⟩ := hex
    have htop : Submodule.span ℤ ({m} : Set (I → ℤ)) = ⊤ := by
      apply top_unique
      rw [← hspan]
      exact Submodule.span_le.mpr hm
    have hdim := finrank_span_le_card (R := ℤ) ({m} : Set (I → ℤ))
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
    simpa [Nat.card_eq_fintype_card] using hdim
  by_cases hne : ∃ m ∈ W, m ≠ 0
  · obtain ⟨m, hm, hm0⟩ := hne
    refine ⟨m, fun p hp => ?_⟩
    by_cases hp0 : p = 0
    · simp [hp0]
    · rcases hpair m hm hm0 p hp hp0 with hpm | hpm
      · rw [hpm]
        exact Submodule.subset_span (Set.mem_singleton m)
      · rw [hpm]
        exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton m))
  · refine ⟨0, fun p hp => ?_⟩
    have hp0 : p = 0 := by
      by_contra hp0
      exact hne ⟨p, hp, hp0⟩
    simp [hp0]

omit [DecidableEq I] in
/-- A generating set in an integer lattice of rank at least two contains two
nonzero vectors that are neither equal nor opposite. -/
theorem exists_nonreciprocal_generators {W : Set (I → ℤ)}
    (hW : AddSubgroup.closure W = ⊤) (hI : 2 ≤ Nat.card I) :
    ∃ m ∈ W, ∃ p ∈ W, m ≠ 0 ∧ p ≠ 0 ∧ p ≠ m ∧ p ≠ -m := by
  by_contra h
  have hp : ∀ m ∈ W, m ≠ 0 → ∀ p ∈ W, p ≠ 0 → p = m ∨ p = -m := by
    intro m hm hm0 p hp hp0
    by_cases hpm : p = m
    · exact Or.inl hpm
    · right
      by_contra hneg
      exact h ⟨m, hm, p, hp, hm0, hp0, hpm, hneg⟩
  have := card_le_one_of_generators_equal_or_neg hW hp
  omega

/-- Over an infinite field, a nonzero integral exponent is nontrivial on
some tuple of field units. -/
theorem exists_exponentValue_ne_one [Infinite k] {m : I → ℤ} (hm : m ≠ 0) :
    ∃ t : I → kˣ, exponentValue I t (Multiplicative.ofAdd m) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  obtain ⟨a, ha⟩ := exists_units_zpow_ne_one (k := k) hi
  refine ⟨Pi.mulSingle i a, ?_⟩
  simpa [exponentValue, Pi.mulSingle_apply] using ha

/-- Exponent monomials on field-unit tuples distinguish all exponent vectors
over an infinite field. -/
theorem exponentValue_function_injective [Infinite k] :
    Function.Injective (fun m : I → ℤ =>
      fun t : I → kˣ => (exponentValue I t (Multiplicative.ofAdd m) : k)) := by
  intro m p h
  apply sub_eq_zero.mp
  by_contra hmp
  obtain ⟨t, ht⟩ := exists_exponentValue_ne_one (k := k) hmp
  apply ht
  have he : exponentValue I t (Multiplicative.ofAdd m) =
      exponentValue I t (Multiplicative.ofAdd p) := Units.ext (congrFun h t)
  change exponentValue I t (Multiplicative.ofAdd m / Multiplicative.ofAdd p) = 1
  rw [map_div, he]
  simp

end splitTorus

namespace MatrixRepresentation

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]
  {N : ℕ} (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) (Fin N))

/-- Two actual nonzero universal coefficient columns whose integral weights
are nonzero, distinct, and not opposite. -/
structure NonreciprocalWeightPair where
  first : I → ℤ
  second : I → ℤ
  first_ne_zero : first ≠ 0
  second_ne_zero : second ≠ 0
  second_ne_first : second ≠ first
  second_ne_neg_first : second ≠ -first
  firstColumn : Fin N
  secondColumn : Fin N
  firstVector_ne_zero :
    GeneralLinear.CocharacterDiagonal.coefficientColumn I ρ first firstColumn ≠ 0
  secondVector_ne_zero :
    GeneralLinear.CocharacterDiagonal.coefficientColumn I ρ second secondColumn ≠ 0

private theorem weight_eq_coefficientColumn (m : I → ℤ) (a b : Fin N) :
    CharacterRestrictionFiniteIndex.weight ρ I (𝟙 _) m a b =
      GeneralLinear.CocharacterDiagonal.coefficientColumn I ρ m b a := by
  simp [CharacterRestrictionFiniteIndex.weight,
    CharacterRestrictionFiniteIndex.universalMatrix,
    GeneralLinear.CocharacterDiagonal.coefficientColumn,
    GeneralLinear.CocharacterDiagonal.universalMatrix]
  rfl

/-- A faithful actual representation of a split torus of dimension at least
two supplies such a pair, in every characteristic. -/
theorem nonempty_nonreciprocalWeightPair [Mono ρ.hom.hom.left]
    (hI : 2 ≤ Nat.card I) : Nonempty (NonreciprocalWeightPair I ρ) := by
  have hmono : Mono ((𝟙 _ : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) I).hom.hom ≫
      ρ.hom.hom).left := by
    change Mono ρ.hom.hom.left
    infer_instance
  obtain ⟨m, hm, p, hp, hm0, hp0, hpm, hneg⟩ :=
    splitTorus.exists_nonreciprocal_generators
      (CharacterRestrictionFiniteIndex.closure_weights_eq_top ρ I (𝟙 _) hmono) hI
  have hex (q : I → ℤ)
      (hq : CharacterRestrictionFiniteIndex.weight ρ I (𝟙 _) q ≠ 0) :
      ∃ j, GeneralLinear.CocharacterDiagonal.coefficientColumn I ρ q j ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    ext a b
    rw [weight_eq_coefficientColumn, h b]
    rfl
  obtain ⟨a, ha⟩ := hex m hm
  obtain ⟨b, hb⟩ := hex p hp
  exact ⟨⟨m, p, hm0, hp0, hpm, hneg, a, b, ha, hb⟩⟩

/-- Choose the actual pair of nonreciprocal universal weight vectors in a
faithful split-torus representation of dimension at least two. -/
def nonreciprocalWeightPair [Mono ρ.hom.hom.left] (hI : 2 ≤ Nat.card I) :
    NonreciprocalWeightPair I ρ :=
  (nonempty_nonreciprocalWeightPair I ρ hI).some

end MatrixRepresentation

end Langlands.GroupScheme
