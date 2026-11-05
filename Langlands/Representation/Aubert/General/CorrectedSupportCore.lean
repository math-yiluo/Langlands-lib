import Langlands.Representation.Aubert.General.CorrectedSupportComparison

/-! # The corrected Weyl core as the largest actual parabolic-invariant support -/

noncomputable section

namespace Langlands.Aubert.General.CorrectedFiltration

open Langlands.Group

universe uI uG

section Cells

variable {G : Type uG} [Group G] (T B : Subgroup G)

/-- An actual `B`-double coset has at most one index in the full-centralizer
Weyl quotient. This is comparison data, without an assertion for arbitrary
subgroups. -/
def CellIndexSeparation : Prop :=
  ∀ n n' : RelativeWeyl.normalizer T,
    DoubleCoset.mk B B (n : G) = DoubleCoset.mk B B (n' : G) →
      (QuotientGroup.mk n : RelativeWeyl.Weyl T) = QuotientGroup.mk n'

variable {T B}

private theorem mem_doubleCoset_iff_mk_eq {A : Type*} [Group A]
    (L R : Subgroup A) (a b : A) :
    b ∈ DoubleCoset.doubleCoset a L R ↔
      DoubleCoset.mk L R a = DoubleCoset.mk L R b := by
  rw [DoubleCoset.mem_doubleCoset, DoubleCoset.eq]
  rfl

/-- A normalizer lift belongs to a union of base cells precisely when its
Weyl class belongs to the index set. -/
theorem normalizer_mem_cellSupport_iff (hsep : CellIndexSeparation T B)
    (θ : Set (RelativeWeyl.Weyl T)) (n : RelativeWeyl.normalizer T) :
    (n : G) ∈ cellSupport T B B θ ↔
      (QuotientGroup.mk n : RelativeWeyl.Weyl T) ∈ θ := by
  constructor
  · rintro ⟨n', hn', b, hb, q, hq, heq⟩
    have hclass := hsep n' n ((mem_doubleCoset_iff_mk_eq B B _ _).mp
      (DoubleCoset.mem_doubleCoset.mpr ⟨b, hb, q, hq, heq⟩))
    exact hclass ▸ hn'
  · intro hn
    exact ⟨n, hn, 1, B.one_mem, 1, B.one_mem, by simp⟩

/-- Every base-cell union is invariant under the two base-subgroup actions. -/
theorem cellSupport_base_invariant (θ : Set (RelativeWeyl.Weyl T)) :
    Support.IsTwoSidedInvariant B B (cellSupport T B B θ) := by
  rintro g ⟨n, hn, b, hb, q, hq, rfl⟩ a ha c hc
  exact ⟨n, hn, a * b, B.mul_mem ha hb, q * c, B.mul_mem hq hc,
    by simp only [mul_assoc]⟩

/-- The largest actual `P`-`Q` invariant subset of a base-cell support equals
the implemented cell union of the largest `H`-`K` invariant Weyl subset.
The actual union on the right uses `B n Q`, as in `groupSupport`. -/
theorem twoSidedCore_cellSupport (P Q : Subgroup G)
    (H K : Subgroup (RelativeWeyl.Weyl T))
    (hBP : B ≤ P) (hBQ : B ≤ Q) (hcover : IsBruhatCover T B B)
    (hsep : CellIndexSeparation T B)
    (hcomp : CellDoubleCosetComparison T P Q H K)
    (θ : Set (RelativeWeyl.Weyl T)) :
    Support.twoSidedCore P Q (cellSupport T B B θ) =
      cellSupport T B Q (Support.twoSidedCore H K θ) := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, b, hb, q, hq, heq⟩ := hcover g
    refine ⟨n, ?_, b, hb, q, hBQ hq, heq⟩
    intro w hw
    obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective w
    apply (normalizer_mem_cellSupport_iff hsep θ n').mp
    apply hg
    apply (mem_doubleCoset_iff_mk_eq P Q _ _).mpr
    have hng : DoubleCoset.mk P Q (n : G) = DoubleCoset.mk P Q g :=
      (mem_doubleCoset_iff_mk_eq P Q _ _).mp
        (DoubleCoset.mem_doubleCoset.mpr ⟨b, hBP hb, q, hBQ hq, heq⟩)
    have hnn' : DoubleCoset.mk P Q (n : G) = DoubleCoset.mk P Q (n' : G) :=
      (hcomp n n').mpr ((mem_doubleCoset_iff_mk_eq H K _ _).mp hw)
    exact hng.symm.trans hnn'
  · rintro ⟨n, hn, b, hb, q, hq, heq⟩ x hx
    obtain ⟨n', b', hb', q', hq', heq'⟩ := hcover x
    refine ⟨n', ?_, b', hb', q', hq', heq'⟩
    apply hn
    apply (mem_doubleCoset_iff_mk_eq H K _ _).mpr
    apply (hcomp n n').mp
    have hng : DoubleCoset.mk P Q (n : G) = DoubleCoset.mk P Q g :=
      (mem_doubleCoset_iff_mk_eq P Q _ _).mp
        (DoubleCoset.mem_doubleCoset.mpr ⟨b, hBP hb, q, hq, heq⟩)
    have hnx : DoubleCoset.mk P Q (n' : G) = DoubleCoset.mk P Q x :=
      (mem_doubleCoset_iff_mk_eq P Q _ _).mp
        (DoubleCoset.mem_doubleCoset.mpr ⟨b', hBP hb', q', hBQ hq', heq'⟩)
    exact (hng.trans ((mem_doubleCoset_iff_mk_eq P Q _ _).mp hx)).trans hnx.symm

end Cells

section FixedOrder

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G]
variable (P : Finset ι → Subgroup G) (T : Subgroup G)
  [Fintype (RelativeWeyl.Weyl T)] [DecidableEq (RelativeWeyl.Weyl T)]
  {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (RelativeWeyl.Weyl T))

/-- The literal corrected support at every list position is the largest
actual two-sided parabolic core of the corresponding base-cell prefix. -/
theorem groupSupport_eq_twoSidedCore (I s : Finset ι) (j : ℕ)
    (hP : Monotone P) (hcover : IsBruhatCover T (P ∅) (P ∅))
    (hsep : CellIndexSeparation T (P ∅))
    (hcomp : CellDoubleCosetComparison T (P (Finset.univ \ s)) (P I)
      (RelativeWeylIndexing.standardSubgroup cs (Finset.univ \ s))
      (RelativeWeylIndexing.standardSubgroup cs I)) :
    groupSupport P T cs I s j =
      Support.twoSidedCore (P (Finset.univ \ s)) (P I)
        (cellSupport T (P ∅) (P ∅) (Support.rankOrderedSupport cs.length j)) := by
  exact (twoSidedCore_cellSupport (P (Finset.univ \ s)) (P I) _ _
    (hP (Finset.empty_subset _)) (hP (Finset.empty_subset _))
    hcover hsep hcomp _).symm

end FixedOrder

end Langlands.Aubert.General.CorrectedFiltration
