import Langlands.Representation.Aubert.General.CorrectedFiltration

/-! Actual function witnesses for a change in the corrected Jacquet filtration. -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

section Cells

variable {G : Type uG} [Group G] {T B Q : Subgroup G}

/-- A point in the difference of two cell unions has an index in the difference
of their Weyl supports. No cell disjointness hypothesis is needed. -/
theorem cellSupport_sdiff_subset {θ η : Set (Group.RelativeWeyl.Weyl T)} :
    cellSupport T B Q θ \ cellSupport T B Q η ⊆ cellSupport T B Q (θ \ η) := by
  rintro g ⟨⟨n, hn, b, hb, q, hq, hg⟩, hprev⟩
  refine ⟨n, ⟨hn, ?_⟩, b, hb, q, hq, hg⟩
  intro hnprev
  exact hprev ⟨n, hnprev, b, hb, q, hq, hg⟩

end Cells

section Standard

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))

/-- An actual induced function in the upper support step whose canonical
Jacquet class does not belong to the lower image step. -/
def IsStepWitness (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι)
    (i : ℕ) (f : term P M U h hclosed A s) : Prop :=
  f ∈ inductionStep P M U h hclosed T cs A I s (i + 1) ∧
    Jacquet.Localization.mk (term P M U h hclosed A s).representation (U I) 1 f ∉
      (step P M U h hclosed T cs A I s i).toSubmodule

variable {P M U h hclosed T cs}

/-- Changing the actual Jacquet image is equivalent to having a witness
in its original smooth induced-function model. -/
theorem step_succ_ne_iff_exists_witness
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) (i : ℕ) :
    step P M U h hclosed T cs A I s (i + 1) ≠ step P M U h hclosed T cs A I s i ↔
      ∃ f, IsStepWitness P M U h hclosed T cs A I s i f := by
  constructor
  · intro hne
    by_contra hnone
    apply hne
    apply le_antisymm
    · intro x hx
      obtain ⟨f, hf, rfl⟩ := (mem_jacquetImage x).mp hx
      by_contra hprev
      exact hnone ⟨f, hf, hprev⟩
    · exact step_monotone A I s (Nat.le_succ i)
  · rintro ⟨f, hf, hprev⟩ heq
    apply hprev
    rw [← heq]
    exact ⟨f, hf, rfl⟩

/-- A witness cannot itself have the lower support: its class would then lie
in the lower Jacquet image by definition. -/
theorem IsStepWitness.not_mem_inductionStep
    {A : SmoothRep.{0, uG, max uG uV} ℂ G} {I s : Finset ι} {i : ℕ}
    {f : term P M U h hclosed A s}
    (hf : IsStepWitness P M U h hclosed T cs A I s i f) :
    f ∉ inductionStep P M U h hclosed T cs A I s i := by
  intro hprev
  exact hf.2 ⟨f, hprev, rfl⟩

/-- Every witness has a nonzero value outside the lower actual group support. -/
theorem IsStepWitness.exists_eval_outside_lower
    {A : SmoothRep.{0, uG, max uG uV} ℂ G} {I s : Finset ι} {i : ℕ}
    {f : term P M U h hclosed A s}
    (hf : IsStepWitness P M U h hclosed T cs A I s i f) :
    ∃ g : G, Induction.eval _ _ f g ≠ 0 ∧
      g ∈ groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i := by
  by_contra hnone
  apply hf.not_mem_inductionStep
  intro g hg
  by_contra hprev
  exact hnone ⟨g, hg, hf.1 g hg, hprev⟩

/-- A changing actual image step occurs only at a minimal representative of
its whole Weyl double coset. -/
theorem minimal_of_step_succ_ne
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) (i : ℕ)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hne : step P M U h hclosed T cs A I s (i + 1) ≠
      step P M U h hclosed T cs A I s i) :
    Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
      (Support.rankOrderedElement cs.length i hi) := by
  by_contra hnot
  exact hne (step_succ_eq A I s i hi hnot)

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- Any point newly entering the actual group support lies in a cell indexed
by the new whole Weyl double coset. -/
theorem groupSupport_succ_sdiff_subset (I s : Finset ι) (i : ℕ)
    (hi : i < (Support.rankOrderedList cs.length).length) :
    groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i ⊆
      cellSupport T (P ∅) (P I)
        (DoubleCoset.doubleCoset (Support.rankOrderedElement cs.length i hi)
          (Group.RelativeWeylIndexing.standardSubgroup cs (Finset.univ \ s))
          (Group.RelativeWeylIndexing.standardSubgroup cs I)) := by
  intro g hg
  have hcell := cellSupport_sdiff_subset hg
  obtain ⟨n, hn, b, hb, q, hq, hg'⟩ := hcell
  refine ⟨n, ?_, b, hb, q, hq, hg'⟩
  by_contra hncoset
  apply hn.2
  rw [modifiedSupport, Support.modifiedRankSupport_step _ _ cs.length i hi]
  exact ⟨hn.1, hncoset⟩

/-- A changing Jacquet step has an actual function witness with a nonzero
value on the cell union indexed by the new Weyl double coset. -/
theorem exists_witness_nonzero_on_doubleCoset
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) (i : ℕ)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hne : step P M U h hclosed T cs A I s (i + 1) ≠
      step P M U h hclosed T cs A I s i) :
    ∃ f, IsStepWitness P M U h hclosed T cs A I s i f ∧
      ∃ g : G, Induction.eval _ _ f g ≠ 0 ∧
        g ∈ cellSupport T (P ∅) (P I)
          (DoubleCoset.doubleCoset (Support.rankOrderedElement cs.length i hi)
            (Group.RelativeWeylIndexing.standardSubgroup cs (Finset.univ \ s))
            (Group.RelativeWeylIndexing.standardSubgroup cs I)) := by
  obtain ⟨f, hf⟩ := (step_succ_ne_iff_exists_witness A I s i).mp hne
  obtain ⟨g, hg, hsupport⟩ := hf.exists_eval_outside_lower
  exact ⟨f, hf, g, hg, groupSupport_succ_sdiff_subset I s i hi hsupport⟩

end Standard

end Langlands.Aubert.General.CorrectedFiltration
