import Langlands.Representation.Aubert.General.CorrectedSupportOpenness

/-! # Cell boundary length from closed products of simple parabolics -/

noncomputable section

namespace Langlands.Aubert.General.CorrectedFiltration

open Langlands.Group
open scoped Pointwise

universe uI uG

variable {ι : Type uI}
variable {G : Type uG} [Group G]
variable (P : Finset ι → Subgroup G)

/-- The product of the simple parabolics in a word, with the base subgroup as
the final factor. This is a subset of the actual group. -/
def parabolicWordSet : List ι → Set G
  | [] => P ∅
  | a :: ω => (P {a} : Set G) * parabolicWordSet ω

/-- Word products are invariant under both base-subgroup actions. -/
theorem parabolicWordSet_base_invariant (hP : Monotone P) (ω : List ι) :
    Support.IsTwoSidedInvariant (P ∅) (P ∅) (parabolicWordSet P ω) := by
  induction ω with
  | nil =>
    intro g hg a ha b hb
    exact (P ∅).mul_mem ((P ∅).mul_mem ha hg) hb
  | cons a ω ih =>
    rintro g ⟨p, hp, y, hy, rfl⟩ b hb c hc
    refine Set.mem_mul.mpr ⟨b * p, (P {a}).mul_mem (hP (Finset.empty_subset _) hb) hp,
      y * c, ?_, by simp only [mul_assoc]⟩
    simpa only [one_mul] using ih y hy 1 (P ∅).one_mem c hc

section Topology

variable [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Compactness of the base quotient and closed parabolics make every finite
word product closed. -/
theorem isClosed_parabolicWordSet
    [CompactSpace (Induction.LeftQuotient (P ∅))]
    (hP : Monotone P) (hclosed : ∀ J, IsClosed (P J : Set G)) (ω : List ι) :
    IsClosed (parabolicWordSet P ω) := by
  induction ω with
  | nil => exact hclosed ∅
  | cons a ω ih =>
    obtain ⟨K, hKP, hKc, hK⟩ := exists_compact_right_representatives_of_compact_quotient
      (P ∅) (P {a}) (hP (Finset.empty_subset _)) (hclosed _)
    have heq : parabolicWordSet P (a :: ω) = K * parabolicWordSet P ω := by
      apply Set.Subset.antisymm
      · rintro g ⟨p, hp, y, hy, rfl⟩
        obtain ⟨k, hk, b, hb, rfl⟩ := hK p hp
        refine Set.mem_mul.mpr ⟨k, hk, b * y, ?_, (mul_assoc _ _ _).symm⟩
        simpa only [mul_one] using
          parabolicWordSet_base_invariant P hP ω y hy b hb 1 (P ∅).one_mem
      · rintro g ⟨k, hk, y, hy, rfl⟩
        exact Set.mem_mul.mpr ⟨k, hKP hk, y, hy, rfl⟩
    rw [heq]
    exact ih.mul_left_of_isCompact hKc

end Topology

variable (T : Subgroup G)
  {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (RelativeWeyl.Weyl T))

private theorem mem_standardSubgroup_singleton {a : ι} {w : RelativeWeyl.Weyl T}
    (hw : w ∈ RelativeWeylIndexing.standardSubgroup cs {a}) :
    w = 1 ∨ w = cs.simple a := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact Or.inr (congrArg cs.simple (Finset.mem_singleton.mp hb))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (cs.simple_mul_simple_self a)
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · exact Or.inl (inv_one)
    · exact Or.inr (cs.inv_simple a)

private theorem normalizer_mem_parabolic_of_index
    (hP : Monotone P)
    (hcomp : ∀ J, CellDoubleCosetComparison T (P J) (P ∅)
      (RelativeWeylIndexing.standardSubgroup cs J) ⊥)
    {J : Finset ι} (n : RelativeWeyl.normalizer T)
    (hn : (QuotientGroup.mk n : RelativeWeyl.Weyl T) ∈
      RelativeWeylIndexing.standardSubgroup cs J) :
    (n : G) ∈ P J := by
  have hweyl : DoubleCoset.mk (RelativeWeylIndexing.standardSubgroup cs J) ⊥
      (1 : RelativeWeyl.Weyl T) =
      DoubleCoset.mk (RelativeWeylIndexing.standardSubgroup cs J) ⊥
        (QuotientGroup.mk n : RelativeWeyl.Weyl T) := by
    rw [DoubleCoset.eq]
    exact ⟨QuotientGroup.mk n, hn, 1, (⊥ : Subgroup _).one_mem, by simp⟩
  have hactual := (hcomp J 1 n).mpr (by simpa using hweyl)
  obtain ⟨p, hp, b, hb, heq⟩ := DoubleCoset.eq.mp hactual
  rw [heq]
  simpa only [Subgroup.coe_one, mul_one] using
    (P J).mul_mem hp (hP (Finset.empty_subset _) hb)

private theorem simple_parabolic_mul_cell
    (hP : Monotone P) (hcover : IsBruhatCover T (P ∅) (P ∅))
    (hcomp : ∀ J, CellDoubleCosetComparison T (P J) (P ∅)
      (RelativeWeylIndexing.standardSubgroup cs J) ⊥)
    {a : ι} {v : RelativeWeyl.Weyl T} {p g : G}
    (hp : p ∈ P {a}) (hg : g ∈ cellSupport T (P ∅) (P ∅) {v}) :
    ∃ v', (v' = v ∨ v' = cs.simple a * v) ∧
      p * g ∈ cellSupport T (P ∅) (P ∅) {v'} := by
  obtain ⟨n, hn, b, hb, q, hq, rfl⟩ := hg
  have hn' : (QuotientGroup.mk n : RelativeWeyl.Weyl T) = v :=
    Set.mem_singleton_iff.mp hn
  obtain ⟨n', b', hb', q', hq', heq'⟩ := hcover (p * (b * (n : G) * q))
  have hng : DoubleCoset.mk (P {a}) (P ∅) (n : G) =
      DoubleCoset.mk (P {a}) (P ∅) (p * (b * (n : G) * q)) := by
    rw [DoubleCoset.eq]
    exact ⟨p * b, (P {a}).mul_mem hp (hP (Finset.empty_subset _) hb),
      q, hq, by simp only [mul_assoc]⟩
  have hn'g : DoubleCoset.mk (P {a}) (P ∅) (n' : G) =
      DoubleCoset.mk (P {a}) (P ∅) (p * (b * (n : G) * q)) := by
    rw [DoubleCoset.eq]
    exact ⟨b', hP (Finset.empty_subset _) hb', q', hq', heq'⟩
  obtain ⟨x, hx, y, hy, hindex⟩ :=
    DoubleCoset.eq.mp ((hcomp {a} n n').mp (hng.trans hn'g.symm))
  have hy' : y = 1 := hy
  rw [hy', mul_one, hn'] at hindex
  refine ⟨QuotientGroup.mk n', ?_, n', rfl, b', hb', q', hq', heq'⟩
  rcases mem_standardSubgroup_singleton T cs hx with hx | hx
  · exact Or.inl (by simpa only [hx, one_mul] using hindex)
  · exact Or.inr (by simpa only [hx] using hindex)

/-- Every cell indexed by a word product lies in the corresponding product
of actual simple parabolics. -/
theorem cellSupport_wordProd_subset
    (hP : Monotone P)
    (hcomp : ∀ J, CellDoubleCosetComparison T (P J) (P ∅)
      (RelativeWeylIndexing.standardSubgroup cs J) ⊥) (ω : List ι) :
    cellSupport T (P ∅) (P ∅) {cs.wordProd ω} ⊆ parabolicWordSet P ω := by
  induction ω with
  | nil =>
    rintro g ⟨n, hn, b, hb, q, hq, rfl⟩
    have hn' := Set.mem_singleton_iff.mp hn
    have hnP : (n : G) ∈ P ∅ := normalizer_mem_parabolic_of_index P T cs hP hcomp n
      (by simpa only [CoxeterSystem.wordProd_nil,
        RelativeWeylIndexing.standardSubgroup_empty, Subgroup.mem_bot] using hn')
    exact (P ∅).mul_mem ((P ∅).mul_mem hb hnP) hq
  | cons a ω ih =>
    rintro g ⟨n, hn, b, hb, q, hq, rfl⟩
    obtain ⟨na, hna⟩ := QuotientGroup.mk_surjective (cs.simple a)
    have hnaP : (na : G) ∈ P {a} := normalizer_mem_parabolic_of_index P T cs hP hcomp na
      (hna.symm ▸ RelativeWeylIndexing.simple_mem_standardSubgroup cs
        (Finset.mem_singleton_self a))
    have htail : (QuotientGroup.mk (na⁻¹ * n) : RelativeWeyl.Weyl T) = cs.wordProd ω := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hna,
        Set.mem_singleton_iff.mp hn, CoxeterSystem.wordProd_cons, inv_mul_cancel_left]
    refine Set.mem_mul.mpr ⟨b * (na : G),
      (P {a}).mul_mem (hP (Finset.empty_subset _) hb) hnaP,
      ((na⁻¹ * n : RelativeWeyl.normalizer T) : G) * q, ?_, ?_⟩
    · apply ih
      exact ⟨na⁻¹ * n, htail, 1, (P ∅).one_mem, q, hq, by simp⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]

/-- Indices occurring in a word product have length at most the word's
length; the unique possible index of full length is its word product. -/
theorem parabolicWordSet_index_bounds
    (hP : Monotone P) (hcover : IsBruhatCover T (P ∅) (P ∅))
    (hcomp : ∀ J, CellDoubleCosetComparison T (P J) (P ∅)
      (RelativeWeylIndexing.standardSubgroup cs J) ⊥)
    (ω : List ι) {g : G} (hg : g ∈ parabolicWordSet P ω) :
    ∃ v : RelativeWeyl.Weyl T,
      g ∈ cellSupport T (P ∅) (P ∅) {v} ∧ cs.length v ≤ ω.length ∧
        (cs.length v = ω.length → v = cs.wordProd ω) := by
  induction ω generalizing g with
  | nil =>
    refine ⟨1, ⟨1, rfl, g, hg, 1, (P ∅).one_mem, by simp⟩, ?_, ?_⟩
    · simp
    · intro _
      simp
  | cons a ω ih =>
    obtain ⟨p, hp, y, hy, rfl⟩ := hg
    obtain ⟨v, hyv, hvlen, hvmax⟩ := ih hy
    obtain ⟨v', hv', hpg⟩ := simple_parabolic_mul_cell P T cs hP hcover hcomp hp hyv
    refine ⟨v', hpg, ?_, ?_⟩
    · rcases hv' with rfl | rfl
      · simpa only [List.length_cons] using hvlen.trans (Nat.le_succ _)
      · have hmul := cs.length_mul_le (cs.simple a) v
        rw [cs.length_simple a] at hmul
        simp only [List.length_cons]
        omega
    · intro hmax
      rcases hv' with rfl | rfl
      · simp only [List.length_cons] at hmax
        omega
      · have hmul := cs.length_mul_le (cs.simple a) v
        rw [cs.length_simple a] at hmul
        simp only [List.length_cons] at hmax
        have hv : cs.length v = ω.length := by omega
        rw [hvmax hv, CoxeterSystem.wordProd_cons]

section Boundary

variable [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [CompactSpace (Induction.LeftQuotient (P ∅))]

/-- Closed word products and the actual parabolic comparison force strict
Coxeter length decrease on every base-cell boundary. -/
theorem cellBoundaryRank_of_parabolicComparisons
    (hP : Monotone P) (hclosed : ∀ J, IsClosed (P J : Set G))
    (hcover : IsBruhatCover T (P ∅) (P ∅))
    (hcomp : ∀ J, CellDoubleCosetComparison T (P J) (P ∅)
      (RelativeWeylIndexing.standardSubgroup cs J) ⊥) :
    CellBoundaryRank T (P ∅) cs.length := by
  intro w g hg
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hgword : g ∈ parabolicWordSet P ω :=
    closure_minimal (cellSupport_wordProd_subset P T cs hP hcomp ω)
      (isClosed_parabolicWordSet P hP hclosed ω) hg.1
  obtain ⟨v, hgv, hvlen, hvmax⟩ :=
    parabolicWordSet_index_bounds P T cs hP hcover hcomp ω hgword
  refine ⟨v, ?_, hgv⟩
  have hvne : cs.length v ≠ ω.length := fun heq => hg.2 (hvmax heq ▸ hgv)
  rw [hω.eq]
  omega

end Boundary

section FixedOrder

variable [LinearOrder ι] [Fintype ι]
variable [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [CompactSpace (Induction.LeftQuotient (P ∅))]
  [Fintype (RelativeWeyl.Weyl T)] [DecidableEq (RelativeWeyl.Weyl T)]

/-- Compactness, the base-cell cover and the actual parabolic comparisons
imply the full fixed-order surviving-support target. Boundary length drop
and index separation are derived rather than assumed. -/
theorem survivingSupportTarget_of_parabolicComparisons
    (hP : Monotone P) (hclosed : ∀ J, IsClosed (P J : Set G))
    (hcover : IsBruhatCover T (P ∅) (P ∅))
    (hcomp : ∀ J I, CellDoubleCosetComparison T (P J) (P I)
      (RelativeWeylIndexing.standardSubgroup cs J)
      (RelativeWeylIndexing.standardSubgroup cs I)) :
    SurvivingSupportTarget P T cs := by
  have hbase : ∀ J, CellDoubleCosetComparison T (P J) (P ∅)
      (RelativeWeylIndexing.standardSubgroup cs J) ⊥ := by
    intro J
    simpa only [RelativeWeylIndexing.standardSubgroup_empty] using hcomp J ∅
  have hsep : CellIndexSeparation T (P ∅) := by
    intro n n' hnn'
    have h := (hbase ∅ n n').mp hnn'
    rw [RelativeWeylIndexing.standardSubgroup_empty, DoubleCoset.eq] at h
    obtain ⟨a, ha, b, hb, heq⟩ := h
    have ha' : a = 1 := ha
    have hb' : b = 1 := hb
    simpa only [ha', hb', one_mul, mul_one] using heq.symm
  exact survivingSupportTarget_of_cellGeometry P T cs hP hclosed hcover hsep hcomp
    (cellBoundaryRank_of_parabolicComparisons P T cs hP hclosed hcover hbase)

end FixedOrder

end Langlands.Aubert.General.CorrectedFiltration
