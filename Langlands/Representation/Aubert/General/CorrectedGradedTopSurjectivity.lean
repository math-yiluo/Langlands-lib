import Langlands.Representation.Aubert.General.CorrectedGradedExactness
import Langlands.Group.RelativeWeylLongestProof

/-!
# Surjectivity of the last graded differential of the corrected filtration

A graded piece of the corrected support filtration with a Boolean contraction
over the survivors at `w` is the constant interval diagram between the left
descents of `w` and `S \ K`, where `W_K = w W_I w⁻¹`. When the two ends differ,
the interval has a free coordinate, so the piece is exact in every degree, and
its differential into degree `|S| - |I|` is surjective. The ends agree only for
one Weyl element: if the left descents of a right-`I`-minimal `w` are exactly
`S \ K`, then `(w a)⁻¹` is the longest element of `W` for the longest `a ∈ W_I`.
So the last graded differential is surjective at every grade other than the
grade of that element.
-/

noncomputable section

namespace Langlands.Group.RelativeWeylIndexing

universe u v

variable {B : Type u} {W : Type v} [Group W]
variable {Mx : CoxeterMatrix B} (cs : CoxeterSystem Mx W)

/-- If `w` is right-`I`-minimal, `W_K = w W_I w⁻¹`, and the left descents of
`w` are exactly `S \ K`, then `(w a)⁻¹ = w₀` for a longest `a ∈ W_I` and a
longest `w₀ ∈ W`. -/
theorem inv_mul_eq_of_leftDescentSet_eq [Fintype B] [DecidableEq B] {I K : Finset B} {w a w₀ : W}
    (hR : ∀ i ∈ I, cs.length w < cs.length (w * cs.simple i))
    (hconj : ∀ x, x ∈ standardSubgroup cs K ↔ w⁻¹ * x * w ∈ standardSubgroup cs I)
    (hD : leftDescentSet cs w = Finset.univ \ K)
    (ha : a ∈ standardSubgroup cs I)
    (haI : ∀ b ∈ standardSubgroup cs I, cs.length b ≤ cs.length a)
    (hw₀ : ∀ x : W, cs.length x ≤ cs.length w₀) :
    (w * a)⁻¹ = w₀ := by
  have hmin : ∀ x ∈ standardSubgroup cs I, cs.length w ≤ cs.length (w * x) := by
    have h := (minimalityLengthCriterion_proof cs ∅ I w).mpr ⟨by simp, hR⟩
    intro x hx
    simpa using h 1 (standardSubgroup cs ∅).one_mem x hx
  have hwa := length_mul_of_right_minimal cs hmin ha
  refine eq_of_forall_length_mul_simple_lt cs hw₀ fun j => ?_
  have hinv : cs.length ((w * a)⁻¹ * cs.simple j) = cs.length (cs.simple j * (w * a)) := by
    rw [← cs.length_inv, mul_inv_rev, inv_inv, cs.inv_simple]
  rw [hinv, cs.length_inv, hwa]
  by_cases hj : j ∈ K
  · have hb : w⁻¹ * cs.simple j * w ∈ standardSubgroup cs I :=
      (hconj _).mp (simple_mem_standardSubgroup cs hj)
    have hrefl : cs.IsReflection (w⁻¹ * cs.simple j * w) := ⟨w⁻¹, j, by rw [inv_inv]⟩
    have heq : cs.simple j * (w * a) = w * ((w⁻¹ * cs.simple j * w) * a) := by group
    rw [heq, length_mul_of_right_minimal cs hmin ((standardSubgroup cs I).mul_mem hb ha)]
    have hle := haI _ ((standardSubgroup cs I).mul_mem hb ha)
    have hne := hrefl.length_mul_right_ne a
    omega
  · have hjD : j ∈ leftDescentSet cs w := by
      rw [hD]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
    have hdesc := (mem_leftDescentSet cs).mp hjD
    have hle := cs.length_mul_le (cs.simple j * w) a
    rw [← mul_assoc]
    rcases cs.length_simple_mul w j with h | h <;> omega

/-- At most one right-`I`-minimal `w` has, for some `K` with
`W_K = w W_I w⁻¹`, exactly `S \ K` as its left descents. -/
theorem eq_of_leftDescentSet_eq [Fintype B] [DecidableEq B] [Fintype W] {I K K' : Finset B} {w w' : W}
    (hR : ∀ i ∈ I, cs.length w < cs.length (w * cs.simple i))
    (hconj : ∀ x, x ∈ standardSubgroup cs K ↔ w⁻¹ * x * w ∈ standardSubgroup cs I)
    (hD : leftDescentSet cs w = Finset.univ \ K)
    (hR' : ∀ i ∈ I, cs.length w' < cs.length (w' * cs.simple i))
    (hconj' : ∀ x, x ∈ standardSubgroup cs K' ↔ w'⁻¹ * x * w' ∈ standardSubgroup cs I)
    (hD' : leftDescentSet cs w' = Finset.univ \ K') :
    w = w' := by
  classical
  obtain ⟨w₀, -, hw₀⟩ := Finset.univ.exists_max_image cs.length Finset.univ_nonempty
  obtain ⟨a, haS, haI⟩ := (Finset.univ.filter (· ∈ standardSubgroup cs I)).exists_max_image
    cs.length ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ 1, (standardSubgroup cs I).one_mem⟩⟩
  have ha : a ∈ standardSubgroup cs I := (Finset.mem_filter.mp haS).2
  have haI' : ∀ b ∈ standardSubgroup cs I, cs.length b ≤ cs.length a :=
    fun b hb => haI b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)
  have hw₀' : ∀ x : W, cs.length x ≤ cs.length w₀ := fun x => hw₀ x (Finset.mem_univ x)
  have h := (inv_mul_eq_of_leftDescentSet_eq cs hR hconj hD ha haI' hw₀').trans
    (inv_mul_eq_of_leftDescentSet_eq cs hR' hconj' hD' ha haI' hw₀').symm
  exact mul_right_cancel (inv_injective h)

end Langlands.Group.RelativeWeylIndexing

namespace Langlands.Aubert.CutComplex

open Langlands.Group.RelativeWeylIndexing

universe uI uM uX

namespace Diagram.Subdiagram

variable {ι : Type uI} [LinearOrder ι] {D : Diagram.{uI,uM} ι} {S U : D.Subdiagram}

namespace BooleanContraction

variable {Surv : Finset ι → Prop} {X : Type uX} [AddCommGroup X] [Module ℂ X]
  (C : S.BooleanContraction U Surv X) {lower upper : Finset ι}
  (hSurv : ∀ s, Surv s ↔ BooleanInterval.Active lower upper s)

variable [Fintype ι]

include C hSurv

/-- With a free coordinate, the graded differential into a degree at least
the top of the surviving interval is surjective. -/
theorem surjective_top (hlu : lower ⊆ upper) (hne : lower ≠ upper) (k : ℕ)
    (hk : upper.card ≤ k + 1) :
    Function.Surjective ((S.quotientDiagram U).degreeDifferential k) := by
  obtain ⟨j, hjU, hjL⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hlu, hne⟩)
  have hex := ((C.booleanEquivalence hSurv).degreeDifferential_exact_iff k).mpr
    (BooleanInterval.exact_of_free_coordinate lower upper X j hjU hjL k)
  have hsub : Subsingleton ((S.quotientDiagram U).Degree (k + 1 + 1)) := by
    have : ∀ s : {s : Finset ι // s.card = k + 1 + 1},
        Subsingleton ((S.quotientDiagram U).Obj s.1) := fun s =>
      S.quotient_subsingleton_of_le U (C.inactive s.1 fun hs => by
        have hcard := Finset.card_le_card ((hSurv s.1).mp hs).2
        have hs2 := s.2
        omega)
    infer_instance
  intro y
  have hy : y ∈ LinearMap.ker ((S.quotientDiagram U).degreeDifferential (k + 1)) :=
    LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
  rw [← hex] at hy
  exact hy

end BooleanContraction

section Survivors

variable [Fintype ι] {W : Type*} [Group W] {Mx : CoxeterMatrix ι}
  (cs : CoxeterSystem Mx W) {I K : Finset ι} {w : W}
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

omit [LinearOrder ι] in
/-- If `W_K = w W_I w⁻¹` and `w` is minimal in `W_K w W_I`, then `|I| ≤ |K|`. -/
theorem card_le_of_conj (hconj : ∀ a, a ∈ standardSubgroup cs K ↔
      w⁻¹ * a * w ∈ standardSubgroup cs I)
    (hmin : IsMinimal cs K I w) : I.card ≤ K.card :=
  card_le_of_conj_mem cs (isMinimal_inv cs hmin) fun i hi => by
    rw [inv_inv]
    apply (hconj _).mpr
    simpa [mul_assoc] using simple_mem_standardSubgroup cs hi

/-- A contraction of a graded piece onto `X` over the survivors at `w`, where
`W_K = w W_I w⁻¹`, some cut set survives and the left descents of `w` are not
all of `S \ K`, has surjective differential into degree `|S| - |I|`. -/
theorem surjective_top_of_survives
    (hconj : ∀ a, a ∈ standardSubgroup cs K ↔ w⁻¹ * a * w ∈ standardSubgroup cs I)
    {s₀ : Finset ι} (hs₀ : Survives cs I K w s₀)
    (C : S.BooleanContraction U (Survives cs I K w) X)
    (hD : leftDescentSet cs w ≠ Finset.univ \ K)
    (k : ℕ) (hk : k + 1 = Fintype.card ι - I.card) :
    Function.Surjective ((S.quotientDiagram U).degreeDifferential k) := by
  have hR := right_length_lt_of_isMinimal cs hs₀.2
  have hSurv := BooleanInterval.survivor_iff_active cs (K := K) hR
  have hact := (hSurv s₀).mp hs₀
  have hcard := card_le_of_conj cs hconj (isMinimal_of_subset_left cs hs₀.2 hs₀.1)
  refine C.surjective_top hSurv (hact.1.trans hact.2) hD k ?_
  rw [Finset.card_univ_sdiff]
  omega

end Survivors

end Diagram.Subdiagram

end Langlands.Aubert.CutComplex

namespace Langlands.Aubert.General.JacquetComplex

open Langlands.Group.RelativeWeylIndexing
open Langlands.Aubert.CutComplex

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J)}
  {hclosed : ∀ J, IsClosed (U J : Set G)}
  {hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J)}
  {hP : Monotone P} {hU : Antitone U}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {IsAssociate : Finset ι → Finset ι → G → Prop}
  {T : Subgroup G} [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} {cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T)}
  {A : SmoothRep.{0, uG, max uG uV} ℂ G} {I : Finset ι} {i : ℕ}
  {Lo Up : (jacquetDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU A I).Subdiagram}

/-- The graded piece has surjective differential into degree `|S| - |I|`,
unless the left descents of the `i`-th length-ordered element `w` are exactly
`S \ K` for a `K` with `W_K = w W_I w⁻¹`. -/
theorem graded_surjective_top
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hLo : ∀ s x, x ∈ Lo.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s i).toSubmodule)
    (hUp : ∀ s x, x ∈ Up.obj s ↔
      x ∈ (CorrectedFiltration.step P M U h hclosed T cs A I s (i + 1)).toSubmodule)
    (hfree : ∀ K : Finset ι,
      (∀ a, a ∈ standardSubgroup cs K ↔
        (Support.rankOrderedElement cs.length i hi)⁻¹ * a *
          Support.rankOrderedElement cs.length i hi ∈ standardSubgroup cs I) →
      (∀ j ∈ I, cs.length (Support.rankOrderedElement cs.length i hi) <
        cs.length (Support.rankOrderedElement cs.length i hi * cs.simple j)) →
      leftDescentSet cs (Support.rankOrderedElement cs.length i hi) ≠ Finset.univ \ K)
    (k : ℕ) (hk : k + 1 = Fintype.card ι - I.card) :
    Function.Surjective ((Lo.quotientDiagram Up).degreeDifferential k) :=
  graded_cases hvan htrans hLevi hA hi hLo hUp
    (fun hle y => by
      have := Lo.degree_subsingleton_of_le Up hle (k + 1)
      exact ⟨0, Subsingleton.elim _ _⟩)
    (fun K _ _ _ _ hconj hs₀ C =>
      Diagram.Subdiagram.surjective_top_of_survives cs hconj hs₀ C
        (hfree K hconj (right_length_lt_of_isMinimal cs hs₀.2)) k hk)

/-- Surjectivity transfers between the associated graded map in the
`FiniteFiltered.gradedMap` form and the graded piece's differential. -/
theorem gradedDifferential_surjective_iff (i k : ℕ) :
    Function.Surjective
        (gradedDifferential.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i k) ↔
      Function.Surjective
        ((gradedDiagram.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i).degreeDifferential k) := by
  constructor
  · intro hf y
    obtain ⟨x, hx⟩ := hf ((gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1)).symm y)
    refine ⟨gradedEquiv P M U h hclosed hδ hP hU T cs A I i k x, ?_⟩
    rw [← gradedEquiv_differential, hx, LinearEquiv.apply_symm_apply]
  · intro hg y
    obtain ⟨x, hx⟩ := hg (gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1) y)
    refine ⟨(gradedEquiv P M U h hclosed hδ hP hU T cs A I i k).symm x, ?_⟩
    apply (gradedEquiv P M U h hclosed hδ hP hU T cs A I i (k + 1)).injective
    rw [gradedEquiv_differential, LinearEquiv.apply_symm_apply, hx]

/-- Let the `i₀`-th length-ordered element `w₀` be right-`I`-minimal with
`W_{K₀} = w₀ W_I w₀⁻¹` and left descents exactly `S \ K₀`. Then at every later
grade the associated graded map into degree `|S| - |I|` is surjective. -/
theorem gradedDifferential_surjective_top_of_leftDescentSet_eq
    (hvan : CorrectedFiltration.CorrectedGradedVanishingTarget.{uI, uG, uV}
      P M U h hclosed hM hL IsAssociate T cs)
    (htrans : CorrectedFiltration.CorrectedGradedTransitionTarget.{uI, uG, uV}
      P M U h hclosed hδ hP hU hM hL IsAssociate T cs)
    (hLevi : actualLeviWeylIdentification T M cs)
    (hA : IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) A)
    {i₀ : ℕ} (hi₀ : i₀ < (Support.rankOrderedList cs.length).length) {K₀ : Finset ι}
    (hconj₀ : ∀ a, a ∈ standardSubgroup cs K₀ ↔
      (Support.rankOrderedElement cs.length i₀ hi₀)⁻¹ * a *
        Support.rankOrderedElement cs.length i₀ hi₀ ∈ standardSubgroup cs I)
    (hR₀ : ∀ j ∈ I, cs.length (Support.rankOrderedElement cs.length i₀ hi₀) <
      cs.length (Support.rankOrderedElement cs.length i₀ hi₀ * cs.simple j))
    (hD₀ : leftDescentSet cs (Support.rankOrderedElement cs.length i₀ hi₀) =
      Finset.univ \ K₀) :
    ∀ k, k + 1 = Complex.terminalDegree I → ∀ i, i₀ < i →
      i < (Support.rankOrderedList cs.length).length →
      Function.Surjective
        (gradedDifferential.{uI, uG, uV} P M U h hclosed hδ hP hU T cs A I i k) := by
  intro k hk i hlt hi
  rw [gradedDifferential_surjective_iff]
  refine graded_surjective_top hvan htrans hLevi hA hi (fun _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) (fun K hconj hR hD => ?_) k hk
  have heq := eq_of_leftDescentSet_eq cs hR hconj hD hR₀ hconj₀ hD₀
  have hidx := congrArg Fin.val ((Support.rankOrderedEquiv cs.length).injective heq)
  simp only at hidx
  omega

end Langlands.Aubert.General.JacquetComplex
