import Langlands.Representation.Aubert.General.CorrectedFiltration

/-! # Actual support comparisons from a normalizer double-coset comparison -/

noncomputable section

namespace Langlands.Aubert.General.CorrectedFiltration

open Langlands.Group

universe uI uG

section Cells

variable {G : Type uG} [Group G] (T B P Q : Subgroup G)
  (H K : Subgroup (RelativeWeyl.Weyl T))

/-- The actual normalizer map identifies precisely the same parabolic double
cosets as the indicated subgroups of the full-centralizer Weyl quotient.
This is comparison data, with no assertion for arbitrary subgroups. -/
def CellDoubleCosetComparison : Prop :=
  ∀ n n' : RelativeWeyl.normalizer T,
    DoubleCoset.mk P Q (n : G) = DoubleCoset.mk P Q (n' : G) ↔
      DoubleCoset.mk H K (QuotientGroup.mk n : RelativeWeyl.Weyl T) =
        DoubleCoset.mk H K (QuotientGroup.mk n' : RelativeWeyl.Weyl T)

variable {T B P Q H K}

private theorem mem_doubleCoset_iff_mk_eq {A : Type*} [Group A]
    (L R : Subgroup A) (a b : A) :
    b ∈ DoubleCoset.doubleCoset a L R ↔
      DoubleCoset.mk L R a = DoubleCoset.mk L R b := by
  rw [DoubleCoset.mem_doubleCoset, DoubleCoset.eq]
  rfl

private theorem invariant_mem_of_doubleCoset
    {θ : Set (RelativeWeyl.Weyl T)} (hθ : Support.IsTwoSidedInvariant H K θ)
    {v w : RelativeWeyl.Weyl T} (hv : v ∈ θ)
    (hw : w ∈ DoubleCoset.doubleCoset v H K) : w ∈ θ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hw
  exact hθ v hv a ha b hb

/-- Membership in an invariant cell union is constant on the actual
parabolic double coset of any normalizer lift. -/
theorem mem_cellSupport_iff_of_mem_parabolicDoubleCoset
    (hBP : B ≤ P) (hcover : IsBruhatCover T B Q)
    (hcomp : CellDoubleCosetComparison T P Q H K)
    {θ : Set (RelativeWeyl.Weyl T)} (hθ : Support.IsTwoSidedInvariant H K θ)
    {n : RelativeWeyl.normalizer T} {g : G}
    (hg : g ∈ DoubleCoset.doubleCoset (n : G) P Q) :
    g ∈ cellSupport T B Q θ ↔
      (QuotientGroup.mk n : RelativeWeyl.Weyl T) ∈ θ := by
  have hng := (mem_doubleCoset_iff_mk_eq P Q _ _).mp hg
  constructor
  · rintro ⟨n', hn', b, hb, q, hq, heq⟩
    have hn'g : DoubleCoset.mk P Q (n' : G) = DoubleCoset.mk P Q g :=
      (mem_doubleCoset_iff_mk_eq P Q _ _).mp
        (DoubleCoset.mem_doubleCoset.mpr ⟨b, hBP hb, q, hq, heq⟩)
    exact invariant_mem_of_doubleCoset hθ hn'
      ((mem_doubleCoset_iff_mk_eq H K _ _).mpr
        ((hcomp n' n).mp (hn'g.trans hng.symm)))
  · intro hn
    obtain ⟨n', b, hb, q, hq, heq⟩ := hcover g
    have hn'g : DoubleCoset.mk P Q (n' : G) = DoubleCoset.mk P Q g :=
      (mem_doubleCoset_iff_mk_eq P Q _ _).mp
        (DoubleCoset.mem_doubleCoset.mpr ⟨b, hBP hb, q, hq, heq⟩)
    refine ⟨n', ?_, b, hb, q, hq, heq⟩
    exact invariant_mem_of_doubleCoset hθ hn
      ((mem_doubleCoset_iff_mk_eq H K _ _).mpr
        ((hcomp n n').mp (hng.trans hn'g.symm)))

/-- An invariant Weyl support gives a support invariant under the actual
left parabolic action. -/
theorem cellSupport_mul_left_of_doubleCosetComparison
    (hBP : B ≤ P) (hcover : IsBruhatCover T B Q)
    (hcomp : CellDoubleCosetComparison T P Q H K)
    {θ : Set (RelativeWeyl.Weyl T)} (hθ : Support.IsTwoSidedInvariant H K θ)
    {p g : G} (hp : p ∈ P) (hg : g ∈ cellSupport T B Q θ) :
    p * g ∈ cellSupport T B Q θ := by
  obtain ⟨n, hn, b, hb, q, hq, rfl⟩ := hg
  apply (mem_cellSupport_iff_of_mem_parabolicDoubleCoset hBP hcover hcomp hθ
    (n := n)
    (DoubleCoset.mem_doubleCoset.mpr
      ⟨p * b, P.mul_mem hp (hBP hb), q, hq, by simp only [mul_assoc]⟩)).mpr
  exact hn

/-- Differences of invariant Weyl supports commute with their actual cell
unions once the parabolic double cosets are correctly compared. -/
theorem cellSupport_sdiff_of_doubleCosetComparison
    (hBP : B ≤ P) (hcover : IsBruhatCover T B Q)
    (hcomp : CellDoubleCosetComparison T P Q H K)
    {θ η : Set (RelativeWeyl.Weyl T)} (hη : Support.IsTwoSidedInvariant H K η) :
    cellSupport T B Q θ \ cellSupport T B Q η = cellSupport T B Q (θ \ η) := by
  ext g
  constructor
  · rintro ⟨⟨n, hn, b, hb, q, hq, heq⟩, hprev⟩
    exact ⟨n, ⟨hn, fun hnη => hprev ⟨n, hnη, b, hb, q, hq, heq⟩⟩,
      b, hb, q, hq, heq⟩
  · rintro ⟨n, ⟨hn, hnη⟩, b, hb, q, hq, heq⟩
    refine ⟨⟨n, hn, b, hb, q, hq, heq⟩, ?_⟩
    intro hgη
    exact hnη ((mem_cellSupport_iff_of_mem_parabolicDoubleCoset hBP hcover hcomp hη
      (DoubleCoset.mem_doubleCoset.mpr ⟨b, hBP hb, q, hq, heq⟩)).mp hgη)

/-- The union of the cells in one whole Weyl double coset is the actual
parabolic double coset of any lift of its index. -/
theorem cellSupport_doubleCoset_of_comparison
    (hBP : B ≤ P) (hcover : IsBruhatCover T B Q)
    (hcomp : CellDoubleCosetComparison T P Q H K) (n : RelativeWeyl.normalizer T) :
    cellSupport T B Q
        (DoubleCoset.doubleCoset (QuotientGroup.mk n : RelativeWeyl.Weyl T) H K) =
      DoubleCoset.doubleCoset (n : G) P Q := by
  ext g
  constructor
  · rintro ⟨n', hn', b, hb, q, hq, heq⟩
    apply (mem_doubleCoset_iff_mk_eq P Q _ _).mpr
    exact ((hcomp n n').mpr ((mem_doubleCoset_iff_mk_eq H K _ _).mp hn')).trans
      ((mem_doubleCoset_iff_mk_eq P Q _ _).mp
        (DoubleCoset.mem_doubleCoset.mpr ⟨b, hBP hb, q, hq, heq⟩))
  · intro hg
    obtain ⟨n', b, hb, q, hq, heq⟩ := hcover g
    refine ⟨n', ?_, b, hb, q, hq, heq⟩
    apply (mem_doubleCoset_iff_mk_eq H K _ _).mpr
    apply (hcomp n n').mp
    exact ((mem_doubleCoset_iff_mk_eq P Q _ _).mp hg).trans
      ((mem_doubleCoset_iff_mk_eq P Q _ _).mp
        (DoubleCoset.mem_doubleCoset.mpr ⟨b, hBP hb, q, hq, heq⟩)).symm

end Cells

section FixedOrder

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G]
variable (P : Finset ι → Subgroup G) (T : Subgroup G)
  [Fintype (RelativeWeyl.Weyl T)] [DecidableEq (RelativeWeyl.Weyl T)]
  {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (RelativeWeyl.Weyl T))

/-- Every implemented modified support is left-parabolic invariant, assuming
the actual normalizer double-coset comparison and Bruhat cover. -/
theorem groupSupport_mul_left_of_doubleCosetComparison
    (I s : Finset ι) (j : ℕ) (hP : Monotone P)
    (hcover : IsBruhatCover T (P ∅) (P I))
    (hcomp : CellDoubleCosetComparison T (P (Finset.univ \ s)) (P I)
      (RelativeWeylIndexing.standardSubgroup cs (Finset.univ \ s))
      (RelativeWeylIndexing.standardSubgroup cs I))
    {p g : G} (hp : p ∈ P (Finset.univ \ s))
    (hg : g ∈ groupSupport P T cs I s j) :
    p * g ∈ groupSupport P T cs I s j :=
  cellSupport_mul_left_of_doubleCosetComparison
    (hP (Finset.empty_subset _)) hcover hcomp
    (Support.modifiedRankSupport_invariant _ _ _ _) hp hg

/-- At a surviving position of the literal decreasing-length list, the
actual support difference is the whole parabolic double coset of `m⁻¹`.
The only additional inputs are the cover and double-coset comparison. -/
theorem groupSupport_succ_sdiff_eq_of_doubleCosetComparison
    (I s : Finset ι) (j : ℕ)
    (hj : j < (Support.rankOrderedList cs.length).length)
    (hP : Monotone P) (hcover : IsBruhatCover T (P ∅) (P I))
    (hcomp : CellDoubleCosetComparison T (P (Finset.univ \ s)) (P I)
      (RelativeWeylIndexing.standardSubgroup cs (Finset.univ \ s))
      (RelativeWeylIndexing.standardSubgroup cs I))
    (m : RelativeWeyl.normalizer T)
    (hm : (QuotientGroup.mk m : RelativeWeyl.Weyl T) =
      (Support.rankOrderedElement cs.length j hj)⁻¹)
    (hmin : RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
      (Support.rankOrderedElement cs.length j hj)) :
    groupSupport P T cs I s (j + 1) \ groupSupport P T cs I s j =
      {g | ∃ p ∈ P (Finset.univ \ s), ∃ q ∈ P I, g = p * (m : G)⁻¹ * q} := by
  have hmem := (mem_modifiedSupport_succ_iff cs (Finset.univ \ s) I j hj).mpr hmin
  have hdiff := Support.modifiedRankSupport_succ_diff
    (RelativeWeylIndexing.standardSubgroup cs (Finset.univ \ s))
    (RelativeWeylIndexing.standardSubgroup cs I) cs.length j hj hmem
  have hm' : (QuotientGroup.mk (m⁻¹) : RelativeWeyl.Weyl T) =
      Support.rankOrderedElement cs.length j hj := by
    rw [QuotientGroup.mk_inv, hm, inv_inv]
  unfold groupSupport modifiedSupport
  rw [cellSupport_sdiff_of_doubleCosetComparison (hP (Finset.empty_subset _))
    hcover hcomp (Support.modifiedRankSupport_invariant _ _ _ _)]
  change cellSupport T (P ∅) (P I)
    (Support.modifiedRankSupport _ _ cs.length (j + 1) \
      Support.modifiedRankSupport _ _ cs.length j) = _
  rw [hdiff, ← hm',
    cellSupport_doubleCoset_of_comparison (hP (Finset.empty_subset _)) hcover hcomp]
  ext g
  exact DoubleCoset.mem_doubleCoset

end FixedOrder

end Langlands.Aubert.General.CorrectedFiltration
