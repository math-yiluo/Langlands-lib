import Langlands.Representation.Aubert.General.CorrectedSupportCore
import Langlands.Representation.Aubert.General.RationalCorrectedSurvivingSupportTarget
import Langlands.Representation.Aubert.CorrectedSupportTopology
import Langlands.Representation.Induction.CompactQuotientProof

/-! # Fixed-order corrected support openness from actual cell geometry -/

noncomputable section

namespace Langlands.Aubert.General.CorrectedFiltration

open Langlands.Group
open scoped Pointwise

universe uI uG

section Boundary

variable {G : Type uG} [Group G] [TopologicalSpace G]
  (T B : Subgroup G)

/-- Every point in the boundary of a base cell belongs to a cell of strictly
smaller rank. This is actual-topology comparison data and supplies no instance
for an arbitrary group or family. -/
def CellBoundaryRank (rank : RelativeWeyl.Weyl T → ℕ) : Prop :=
  ∀ (w : RelativeWeyl.Weyl T) (g : G),
    g ∈ closure (cellSupport T B B {w}) \ cellSupport T B B {w} →
      ∃ v : RelativeWeyl.Weyl T,
        rank v < rank w ∧ g ∈ cellSupport T B B {v}

variable {T B}

omit [TopologicalSpace G] in
private theorem cellSupport_indices_eq (hsep : CellIndexSeparation T B)
    {θ η : Set (RelativeWeyl.Weyl T)} {g : G}
    (hgθ : g ∈ cellSupport T B B θ) (hgη : g ∈ cellSupport T B B η) :
    ∃ w, w ∈ θ ∧ w ∈ η := by
  obtain ⟨n, hn, b, hb, q, hq, heq⟩ := hgθ
  obtain ⟨n', hn', b', hb', q', hq', heq'⟩ := hgη
  have hng : DoubleCoset.mk B B (n : G) = DoubleCoset.mk B B g := by
    rw [DoubleCoset.eq]
    exact ⟨b, hb, q, hq, heq⟩
  have hn'g : DoubleCoset.mk B B (n' : G) = DoubleCoset.mk B B g := by
    rw [DoubleCoset.eq]
    exact ⟨b', hb', q', hq', heq'⟩
  exact ⟨QuotientGroup.mk n, hn, (hsep n n' (hng.trans hn'g.symm)).symm ▸ hn'⟩

/-- A finite base-cell support is open when its index set contains every
strictly higher rank and every actual cell boundary strictly lowers rank.
No condition is imposed on the choices among equal-rank indices. -/
theorem isOpen_cellSupport_of_rank_upper [Fintype (RelativeWeyl.Weyl T)]
    (rank : RelativeWeyl.Weyl T → ℕ)
    (hcover : IsBruhatCover T B B) (hsep : CellIndexSeparation T B)
    (hboundary : CellBoundaryRank T B rank)
    (θ : Set (RelativeWeyl.Weyl T)) (hθ : Support.IsRankUpper rank θ) :
    IsOpen (cellSupport T B B θ) := by
  classical
  let E := ⋃ w : {w : RelativeWeyl.Weyl T // w ∉ θ}, cellSupport T B B {w.val}
  have hclosed : IsClosed E := by
    apply isClosed_of_closure_subset
    dsimp only [E]
    rw [closure_iUnion_of_finite]
    rintro g hg
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
    apply Set.mem_iUnion.mpr
    by_cases hgw : g ∈ cellSupport T B B {w.val}
    · exact ⟨w, hgw⟩
    · obtain ⟨v, hv, hgv⟩ := hboundary w.val g ⟨hw, hgw⟩
      have hvθ : v ∉ θ := fun hvθ => w.property (hθ v hvθ w.val hv)
      exact ⟨⟨v, hvθ⟩, hgv⟩
  have hcompl : cellSupport T B B θ = Eᶜ := by
    ext g
    constructor
    · intro hg hE
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hE
      obtain ⟨v, hv, hveq⟩ := cellSupport_indices_eq hsep hg hw
      exact w.property ((Set.mem_singleton_iff.mp hveq) ▸ hv)
    · intro hg
      obtain ⟨n, b, hb, q, hq, heq⟩ := hcover g
      by_cases hn : (QuotientGroup.mk n : RelativeWeyl.Weyl T) ∈ θ
      · exact ⟨n, hn, b, hb, q, hq, heq⟩
      · exact False.elim (hg (Set.mem_iUnion.mpr
          ⟨⟨QuotientGroup.mk n, hn⟩, n, rfl, b, hb, q, hq, heq⟩))
  rw [hcompl]
  exact hclosed.isOpen_compl

end Boundary

section Representatives

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Compactness of the actual base left quotient gives a compact set of left
base-coset representatives inside every closed subgroup containing the base. -/
theorem exists_compact_representatives_of_compact_quotient
    (B P : Subgroup G) [CompactSpace (Induction.LeftQuotient B)]
    (hBP : B ≤ P) (hP : IsClosed (P : Set G)) :
    ∃ K : Set G, K ⊆ P ∧ IsCompact K ∧
      ∀ p ∈ P, ∃ b ∈ B, ∃ k ∈ K, p = b * k := by
  classical
  obtain ⟨K₀, hK₀c, -⟩ := compactOpenSubgroupBasis G Set.univ Filter.univ_mem
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover B K₀
  let C : Set G := (t : Set G) * (K₀ : Set G)
  have hCc : IsCompact C := t.finite_toSet.isCompact.mul hK₀c
  refine ⟨C ∩ P, fun _ h => h.2, hCc.inter_right hP, ?_⟩
  intro p hp
  obtain ⟨i, hi, b, hb, k, hk, heq⟩ := ht p
  have hik : i * k ∈ P := by
    have h := P.mul_mem (P.inv_mem (hBP hb)) hp
    rw [heq] at h
    simpa only [mul_assoc, inv_mul_cancel_left] using h
  exact ⟨b, hb, i * k, ⟨Set.mem_mul.mpr ⟨i, hi, k, hk, rfl⟩, hik⟩,
    by simpa only [mul_assoc] using heq⟩

/-- Inverting compact left representatives gives compact right representatives. -/
theorem exists_compact_right_representatives_of_compact_quotient
    (B Q : Subgroup G) [CompactSpace (Induction.LeftQuotient B)]
    (hBQ : B ≤ Q) (hQ : IsClosed (Q : Set G)) :
    ∃ L : Set G, L ⊆ Q ∧ IsCompact L ∧
      ∀ q ∈ Q, ∃ l ∈ L, ∃ b ∈ B, q = l * b := by
  obtain ⟨K, hKQ, hKc, hK⟩ :=
    exists_compact_representatives_of_compact_quotient B Q hBQ hQ
  refine ⟨Inv.inv '' K, ?_, hKc.image continuous_inv, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact Q.inv_mem (hKQ hk)
  · intro q hq
    obtain ⟨b, hb, k, hk, heq⟩ := hK q⁻¹ (Q.inv_mem hq)
    exact ⟨k⁻¹, ⟨k, hk, rfl⟩, b⁻¹, B.inv_mem hb,
      by simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv heq⟩

end Representatives

section FixedOrder

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
variable (P : Finset ι → Subgroup G) (T : Subgroup G)
  [Fintype (RelativeWeyl.Weyl T)] [DecidableEq (RelativeWeyl.Weyl T)]
  {CM : CoxeterMatrix ι} (cs : CoxeterSystem CM (RelativeWeyl.Weyl T))

/-- Actual cell-boundary rank drop and compactness of the base quotient imply
openness of every implemented corrected support, including every tie choice. -/
theorem isOpen_groupSupport_of_cellGeometry
    [CompactSpace (Induction.LeftQuotient (P ∅))]
    (I s : Finset ι) (j : ℕ) (hP : Monotone P)
    (hclosed : ∀ J, IsClosed (P J : Set G))
    (hcover : IsBruhatCover T (P ∅) (P ∅))
    (hsep : CellIndexSeparation T (P ∅))
    (hcomp : CellDoubleCosetComparison T (P (Finset.univ \ s)) (P I)
      (RelativeWeylIndexing.standardSubgroup cs (Finset.univ \ s))
      (RelativeWeylIndexing.standardSubgroup cs I))
    (hboundary : CellBoundaryRank T (P ∅) cs.length) :
    IsOpen (groupSupport P T cs I s j) := by
  obtain ⟨K, hKP, hKc, hK⟩ := exists_compact_representatives_of_compact_quotient
    (P ∅) (P (Finset.univ \ s)) (hP (Finset.empty_subset _)) (hclosed _)
  obtain ⟨L, hLQ, hLc, hL⟩ := exists_compact_right_representatives_of_compact_quotient
    (P ∅) (P I) (hP (Finset.empty_subset _)) (hclosed _)
  rw [groupSupport_eq_twoSidedCore P T cs I s j hP hcover hsep hcomp]
  exact Support.isOpen_twoSidedCore_of_compact_representatives
    (P ∅) (P (Finset.univ \ s)) (P I) K L hKP hLQ hK hL
    (cellSupport T (P ∅) (P ∅) (Support.rankOrderedSupport cs.length j))
    (cellSupport_base_invariant _) hKc hLc
    (isOpen_cellSupport_of_rank_upper cs.length hcover hsep hboundary _
      (Support.rankOrderedSupport_isRankUpper cs.length j))

/-- The exact four-field surviving-support target follows from actual base-cell
geometry, parabolic comparisons and compactness of the base left quotient.
These inputs are retained explicitly; the rational instances are not asserted. -/
theorem survivingSupportTarget_of_cellGeometry
    [CompactSpace (Induction.LeftQuotient (P ∅))]
    (hP : Monotone P) (hclosed : ∀ J, IsClosed (P J : Set G))
    (hcover : IsBruhatCover T (P ∅) (P ∅))
    (hsep : CellIndexSeparation T (P ∅))
    (hcomp : ∀ J I, CellDoubleCosetComparison T (P J) (P I)
      (RelativeWeylIndexing.standardSubgroup cs J)
      (RelativeWeylIndexing.standardSubgroup cs I))
    (hboundary : CellBoundaryRank T (P ∅) cs.length) :
    SurvivingSupportTarget P T cs := by
  intro I s j hj m hm hmin
  have hcoverI : IsBruhatCover T (P ∅) (P I) := by
    intro g
    obtain ⟨n, b, hb, q, hq, heq⟩ := hcover g
    exact ⟨n, b, hb, q, hP (Finset.empty_subset _) hq, heq⟩
  exact ⟨isOpen_groupSupport_of_cellGeometry P T cs I s j hP hclosed
      hcover hsep (hcomp _ _) hboundary,
    isOpen_groupSupport_of_cellGeometry P T cs I s (j + 1) hP hclosed
      hcover hsep (hcomp _ _) hboundary,
    fun p hp g hg => groupSupport_mul_left_of_doubleCosetComparison P T cs I s
      (j + 1) hP hcoverI (hcomp _ _) hp hg,
    groupSupport_succ_sdiff_eq_of_doubleCosetComparison P T cs I s j hj
      hP hcoverI (hcomp _ _) m hm hmin⟩

end FixedOrder

end Langlands.Aubert.General.CorrectedFiltration
