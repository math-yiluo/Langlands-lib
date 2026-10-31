import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-!
# Actual subquotients selected by multiplicity excess

Finite composition-series multiplicities locate an actual quotient of an
actual subrepresentation in a grade other than a specified contribution.
The grades need no separately supplied finite-length hypotheses.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Langlands.WeylBranchPieces

universe uG uV uW uX uC vC

variable {G : Type uG} [Group G]

/-- Positive actual composition-series multiplicity supplies an actual
quotient of a subrepresentation. -/
theorem isSubquotient_of_positive_multiplicity
    {A : Rep.{uV} ℂ G} {τ : Rep.{uW} ℂ G} {m : ℕ}
    (hm : HasJordanHolderMultiplicity A τ m) (hpos : 0 < m) :
    IsSubquotient A.ρ τ.ρ := by
  obtain ⟨n, s, -, hc⟩ := hm
  have hp : 0 < Nat.card {i : Fin n //
      Nonempty ((s.gradedRepresentation i).ρ.Equiv τ.ρ)} := by
    change 0 < s.factorMultiplicity τ
    rwa [hc]
  obtain ⟨⟨i, ⟨e⟩⟩⟩ := (Nat.card_pos_iff.mp hp).1
  exact (isSubquotient_graded s (Discrete.mk PUnit.unit) i).of_equiv_right e

/-- The ambient finite series supplies finite series for every grade, and
their actual multiplicities sum to the supplied ambient multiplicity. -/
theorem grade_multiplicities
    {A : Rep.{uV} ℂ G} {τ : Rep.{uW} ℂ G} {M n : ℕ}
    (s : ObjectRepFiltration A n) (hM : HasJordanHolderMultiplicity A τ M) :
    ∃ counts : Fin n → ℕ,
      (∀ i, HasJordanHolderMultiplicity (s.gradedRepresentation i) τ (counts i)) ∧
      (∑ i, counts i) = M := by
  obtain ⟨N, t, ht, hc⟩ := hM
  obtain ⟨lengths, counts, H, -, hsum⟩ :=
    jordanHolderFiltrationDecomposition ℂ G A τ N M n
      ⟨t, ht⟩ ⟨N, t, ht, hc⟩ s
  refine ⟨counts, ?_, hsum⟩
  intro i
  obtain ⟨r, hr, hcount⟩ := H i
  exact ⟨lengths i, r, hr, hcount⟩

/-- If the ambient count exceeds that of one identified grade, another
grade has positive actual multiplicity and contains the specified actual
subquotient. No irreducibility or finite-length premise on each grade is
needed. -/
theorem exists_isSubquotient_graded_of_multiplicity_excess
    {A : Rep.{uV} ℂ G} {B : Rep.{uX} ℂ G} {τ : Rep.{uW} ℂ G}
    {n b M : ℕ} (s : ObjectRepFiltration A n) (i₀ : Fin n)
    (e₀ : (s.gradedRepresentation i₀).ρ.Equiv B.ρ)
    (hb : HasJordanHolderMultiplicity B τ b)
    (hM : HasJordanHolderMultiplicity A τ M) (hexcess : b < M) :
    ∃ i : Fin n, i ≠ i₀ ∧ IsSubquotient (s.gradedRepresentation i).ρ τ.ρ := by
  classical
  obtain ⟨counts, hcounts, hsum⟩ := grade_multiplicities s hM
  have hc₀ : counts i₀ = b :=
    HasJordanHolderMultiplicity.unique
      ((equivJordanHolderMultiplicityTransport ℂ G (s.gradedRepresentation i₀) B
        τ τ e₀ (Representation.Equiv.refl _) (counts i₀)).mp (hcounts i₀)) hb
  have hother : ∃ i : Fin n, i ≠ i₀ ∧ 0 < counts i := by
    by_contra h
    have hz : ∀ i : Fin n, i ≠ i₀ → counts i = 0 := by
      intro i hi
      have hn : ¬ 0 < counts i := fun hp => h ⟨i, hi, hp⟩
      omega
    have heq : (∑ i, counts i) = counts i₀ :=
      Finset.sum_eq_single i₀ (fun i _ hi => hz i hi) (by simp)
    omega
  obtain ⟨i, hi, hpos⟩ := hother
  exact ⟨i, hi, isSubquotient_of_positive_multiplicity (hcounts i) hpos⟩

/-- Actual data for the other grade selected by strict multiplicity excess:
its index, an invariant subspace and a surjective intertwiner onto the
specified representation. -/
def excessGradeSubquotientWitness
    {A : Rep.{uV} ℂ G} {B : Rep.{uX} ℂ G} {τ : Rep.{uW} ℂ G}
    {n b M : ℕ} (s : ObjectRepFiltration A n) (i₀ : Fin n)
    (e₀ : (s.gradedRepresentation i₀).ρ.Equiv B.ρ)
    (hb : HasJordanHolderMultiplicity B τ b)
    (hM : HasJordanHolderMultiplicity A τ M) (hexcess : b < M) :
    Σ i : {i : Fin n // i ≠ i₀},
      Σ U : Subrepresentation (s.gradedRepresentation i.val).ρ,
        {q : U.toRepresentation.IntertwiningMap τ.ρ // Function.Surjective q} := by
  apply Classical.choice
  obtain ⟨i, hi, U, q, hq⟩ :=
    exists_isSubquotient_graded_of_multiplicity_excess s i₀ e₀ hb hM hexcess
  exact ⟨⟨⟨i, hi⟩, U, q, hq⟩⟩

variable {C : Type uC} [Category.{vC} C]

/-- The same exclusion holds for the named pieces of an unordered natural
filtration, independently of its chosen order. -/
theorem IsGluedFrom.exists_isSubquotient_piece_of_multiplicity_excess
    {F : C ⥤ Rep.{uV} ℂ G} {n b M : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} ℂ G}
    (h : Langlands.IsGluedFrom F pieces) (Y : C) (i₀ : Fin n)
    {τ : Rep.{uW} ℂ G}
    (hb : HasJordanHolderMultiplicity ((pieces i₀).obj Y) τ b)
    (hM : HasJordanHolderMultiplicity (F.obj Y) τ M) (hexcess : b < M) :
    ∃ i : Fin n, i ≠ i₀ ∧ IsSubquotient ((pieces i).obj Y).ρ τ.ρ := by
  obtain ⟨e, s, hs⟩ := h
  let t : ObjectRepFiltration (F.obj Y) n :=
    ObjectRepFiltration.ofSubrepresentations (fun i => (s.step i).obj Y)
      (s.monotone Y) (s.zero Y) (s.top Y)
  obtain ⟨φ₀⟩ := hs (e.symm i₀)
  have hi₀ : (pieces ∘ e) (e.symm i₀) = pieces i₀ := by simp
  rw [hi₀] at φ₀
  let E₀ : (t.gradedRepresentation (e.symm i₀)).ρ.Equiv ((pieces i₀).obj Y).ρ :=
    Representation.equivOfIso (φ₀.app Y)
  obtain ⟨j, hj, hq⟩ :=
    exists_isSubquotient_graded_of_multiplicity_excess t (e.symm i₀) E₀ hb hM hexcess
  refine ⟨e j, ?_, ?_⟩
  · intro heq
    exact hj (by simpa using congrArg e.symm heq)
  · obtain ⟨φ⟩ := hs j
    exact IsSubquotient.of_equiv_left (Representation.equivOfIso (φ.app Y)).symm hq

end Langlands.WeylBranchPieces
