import Langlands.Representation.Archimedean.RealInducedPairPositiveCrossedQuotient

/-! # The actual kernel remaining in the positive crossed quotient -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairPositiveCrossedKernel

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier
open RealCharacterPair RealCharacterPairReducible
open RealInducedPairAscendingExchange RealInducedPairLinkedReplacement

namespace C
export RealInducedPairPositiveCrossedQuotient (source middleTail middleTailData cutoff_pos
  middle_parity middleTail_section quotient quotient_spec)
end C

namespace M
export RealInducedPairCrossedMiddleQuotient (leftParity rightParity middleList quotient outer_parity)
end M

namespace D
export RealInducedPairDistantParity (innerBinomial innerSection outerPiece outerSection
  outerBinomial middle exists_ascendingData outer_decomposition inner_decomposition)
end D

section Linear

variable {X J V W : Type*}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup J] [Module ℂ J]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A split middle map gives the kernel after passing through a surjective presentation. -/
theorem ker_of_split (A : X →ₗ[ℂ] V) (B : X →ₗ[ℂ] J) (s : J →ₗ[ℂ] X)
    (U : J →ₗ[ℂ] W) (q : V →ₗ[ℂ] W) (hA : Function.Surjective A)
    (hBs : ∀ z, B (s z) = z) (hfac : q.comp A = U.comp B) :
    LinearMap.ker q =
      (LinearMap.ker B).map A ⊔ (LinearMap.ker U).map (A.comp s) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨x, rfl⟩ := hA v
    have hBx : B (x - s (B x)) = 0 := by rw [map_sub, hBs, sub_self]
    have hUx : U (B x) = 0 := by
      rw [← LinearMap.comp_apply, ← hfac]
      exact LinearMap.mem_ker.mp hv
    refine Submodule.mem_sup.mpr
      ⟨A (x - s (B x)), ⟨x - s (B x), hBx, rfl⟩,
        A (s (B x)), ⟨B x, hUx, rfl⟩, ?_⟩
    rw [map_sub]
    abel
  · apply sup_le
    · rintro v ⟨x, hx, rfl⟩
      change q (A x) = 0
      rw [show q (A x) = U (B x) from LinearMap.congr_fun hfac x,
        LinearMap.mem_ker.mp hx, map_zero]
    · rintro v ⟨z, hz, rfl⟩
      change q (A (s z)) = 0
      rw [show q (A (s z)) = U (B (s z)) from LinearMap.congr_fun hfac (s z),
        hBs, LinearMap.mem_ker.mp hz]

/-- A two-piece spanning identity remains a sum of ranges after any linear map. -/
theorem range_of_spanning (L : X →ₗ[ℂ] V) (F : J →ₗ[ℂ] X) (s : W →ₗ[ℂ] X)
    (hspan : ∀ x, ∃ z r, F z + s r = x) :
    LinearMap.range L = LinearMap.range (L.comp F) ⊔ LinearMap.range (L.comp s) := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    obtain ⟨z, r, hx⟩ := hspan x
    refine Submodule.mem_sup.mpr ⟨L (F z), ⟨z, rfl⟩, L (s r), ⟨r, rfl⟩, ?_⟩
    rw [← map_add, hx]
  · exact sup_le (LinearMap.range_comp_le_range F L) (LinearMap.range_comp_le_range s L)

theorem comp_section_of_factorization (A : X →ₗ[ℂ] V) (B : X →ₗ[ℂ] J)
    (s : J →ₗ[ℂ] X) (U : J →ₗ[ℂ] W) (q : V →ₗ[ℂ] W)
    (hBs : ∀ z, B (s z) = z) (hfac : q.comp A = U.comp B) :
    q.comp (A.comp s) = U := by
  apply LinearMap.ext
  intro z
  exact (LinearMap.congr_fun hfac (s z)).trans (congrArg U (hBs z))

end Linear

section Prefix

variable {n : ℕ} {X V Z R W : List RealBlock}

theorem realize_prefix (L : KF n X →ₗ[ℂ] KF n V)
    (F : KF n Z →ₗ[ℂ] KF n X) (s : KF n R →ₗ[ℂ] KF n X)
    (q : KF n W →ₗ[ℂ] KF n V)
    (hL : IsRealIntertwinerModulo n X V ⊥ L)
    (hs : IsRealIntertwinerModulo n R X (LinearMap.range F) s)
    (hr : LinearMap.range q = LinearMap.range (L.comp F))
    (hspan : ∀ x, ∃ z r, F z + s r = x) :
    IsRealIntertwinerModulo n R V (LinearMap.range q) (L.comp s) ∧
    LinearMap.range L = LinearMap.range q ⊔ LinearMap.range (L.comp s) :=
  ⟨modulo_mono (RealInducedPairDistantFiltration.modulo_comp_range hL hs)
      (le_of_eq hr.symm),
    (range_of_spanning L F s hspan).trans
      (congrArg (fun N => N ⊔ LinearMap.range (L.comp s)) hr.symm)⟩

end Prefix

variable {d e : ComplexCharacterData} {k : ℕ}

abbrev originalQuotient (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :=
  P.quotientMap d e (M.leftParity d) (M.rightParity d e k) hd he

/-- The original last binomial followed by the original quotient. -/
def prefixMap (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    KF 4 (X1 d e (M.leftParity d) (M.rightParity d e k)) →ₗ[ℂ]
      KF 4 [.induced d, .induced e] :=
  (originalQuotient (k := k) hd he).comp
    (D.innerBinomial d e k (M.leftParity d) (M.rightParity d e k))

/-- The actual light-source map whose mixed quotient kernel is still to be absorbed. -/
def middleSection (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 (M.middleList d e k) →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  (originalQuotient (k := k) hd he).comp (D.innerSection h (M.outer_parity hH) hH)

theorem ker_middleTail (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.ker (C.middleTail h hH) =
      LinearMap.range (D.innerBinomial d e k (M.leftParity d) (M.rightParity d e k)) :=
  RealInducedPairQuotientPresentation.ker_tail_eq_range (C.cutoff_pos hH)
    (pairParity_eq _ _) (C.middle_parity hH) (neg_one_pow_sq_fin _)
    (data_q0 (n := 4)
      (pre := [.character (P.lo d (M.leftParity d))])
      (post := [.character (P.hi e (M.rightParity d e k))])
      (c := P.hi d (M.leftParity d)) (d := P.lo e (M.rightParity d e k))
      (ℓ := (innerWeight d e k).toNat) rfl)
    (data_B (n := 4)
      (pre := [.character (P.lo d (M.leftParity d))])
      (post := [.character (P.hi e (M.rightParity d e k))])
      (c := P.hi d (M.leftParity d)) (d := P.lo e (M.rightParity d e k))
      (ℓ := (innerWeight d e k).toNat) rfl)
    (C.middleTailData h hH)

/-- The kernel of the actual positive crossed quotient has one explicit unresolved summand. -/
theorem ker_quotient (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.ker (C.quotient hd he h hH) =
      LinearMap.range (prefixMap (k := k) hd he) ⊔
        (LinearMap.ker (M.quotient hd he h hH)).map (middleSection hd he h hH) := by
  have hh := ker_of_split (originalQuotient (k := k) hd he) (C.middleTail h hH)
    (D.innerSection h (M.outer_parity hH) hH) (M.quotient hd he h hH)
    (C.quotient hd he h hH)
    (RealInducedPairQuotientPresentation.quotient_surjective d e
      (M.leftParity d) (M.rightParity d e k) hd he)
    (C.middleTail_section h hH) (C.quotient_spec hd he h hH).2.1
  rw [ker_middleTail h hH, ← LinearMap.range_comp] at hh
  exact hh

theorem prefix_le_ker (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.range (prefixMap (k := k) hd he) ≤
      LinearMap.ker (C.quotient hd he h hH) := by
  rw [ker_quotient hd he h hH]
  exact le_sup_left

theorem prefix_exact (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (X1 d e (M.leftParity d) (M.rightParity d e k))
      [.induced d, .induced e] ⊥ (prefixMap (k := k) hd he) :=
  modulo_comp_bot
    (RealInducedPairQuotientPresentation.quotient_exact d e
      (M.leftParity d) (M.rightParity d e k) hd he)
    (RealInducedPairDistantParity.innerBinomial_exact h (M.outer_parity hH) hH)

theorem middleSection_modulo (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (M.middleList d e k) [.induced d, .induced e]
      (LinearMap.range (prefixMap (k := k) hd he)) (middleSection hd he h hH) :=
  RealInducedPairDistantFiltration.modulo_comp_range
    (RealInducedPairQuotientPresentation.quotient_exact d e
      (M.leftParity d) (M.rightParity d e k) hd he)
    (D.inner_decomposition h (M.outer_parity hH) hH).1

theorem quotient_middleSection (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    (C.quotient hd he h hH).comp (middleSection hd he h hH) =
      M.quotient hd he h hH :=
  comp_section_of_factorization (originalQuotient (k := k) hd he)
    (C.middleTail h hH) (D.innerSection h (M.outer_parity hH) hH)
    (M.quotient hd he h hH) (C.quotient hd he h hH)
    (C.middleTail_section h hH) (C.quotient_spec hd he h hH).2.1

/-- The prefix is realized by an exchanged pair and an allowed outer mixed source. -/
theorem prefix_realization (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    ∃ (qW : KF 4 [.induced e, .induced d] →ₗ[ℂ] KF 4 [.induced d, .induced e])
      (qR : KF 4 (D.outerPiece d e k (M.leftParity d) (M.rightParity d e k)) →ₗ[ℂ]
        KF 4 [.induced d, .induced e]),
      IsRealIntertwinerModulo 4 [.induced e, .induced d] [.induced d, .induced e] ⊥ qW ∧
      IsRealIntertwinerModulo 4
        (D.outerPiece d e k (M.leftParity d) (M.rightParity d e k))
        [.induced d, .induced e] (LinearMap.range qW) qR ∧
      LinearMap.range (prefixMap (k := k) hd he) =
        LinearMap.range qW ⊔ LinearMap.range qR := by
  obtain ⟨μ₀, μ₂, hm, hn0, hn2⟩ :=
    D.exists_ascendingData h (M.outer_parity hH) hH
  obtain ⟨hq, hfac, hrange⟩ := hm.swap_descend he hd
  let F := (D.middle hm).comp
    (D.outerBinomial d e k (M.leftParity d) (M.rightParity d e k))
  let s := (D.middle hm).comp (D.outerSection h (M.outer_parity hH))
  have hword : hm.beforeDescent he hd = (prefixMap (k := k) hd he).comp F :=
    (RealInducedPairDistantParity.beforeDescent_eq hm hd he).trans
      (LinearMap.comp_assoc F
        (D.innerBinomial d e k (M.leftParity d) (M.rightParity d e k))
        (originalQuotient (k := k) hd he)).symm
  have hr : LinearMap.range (hm.swap he hd) =
      LinearMap.range ((prefixMap (k := k) hd he).comp F) :=
    hrange.trans (congrArg LinearMap.range hword)
  have hs := RealInducedPairDistantFiltration.modulo_comp_range
    (RealInducedPairDistantParity.middle_exact hm)
    (D.outer_decomposition h (M.outer_parity hH)).1
  have hspan := RealInducedPairDistantFiltration.span_comp (D.middle hm) _ _
    (RealInducedPairDistantParity.middle_surjective hm hn0 hn2)
    (D.outer_decomposition h (M.outer_parity hH)).2
  have hh := realize_prefix (prefixMap (k := k) hd he) F s (hm.swap he hd)
    (prefix_exact hd he h hH) hs hr hspan
  exact ⟨hm.swap he hd, (prefixMap (k := k) hd he).comp s, hq, hh⟩

theorem outer_allowed (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsAdjacentPiece [] [] (.induced d) (.induced e)
      (D.outerPiece d e k (M.leftParity d) (M.rightParity d e k)) := by
  refine ⟨D.outerPiece d e k (M.leftParity d) (M.rightParity d e k), rfl,
    Or.inr ⟨RealInducedPairDistantParity.outer_support h, ?_⟩⟩
  rw [RealInducedPairDistantParity.outer_weightSquareSum]
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hP : d.weight.natAbs + e.weight.natAbs < outerWeight d e k := by omega
  simp only [realWeightSquareSum, realBlockWeightSquare, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hpow := Nat.pow_lt_pow_left hP two_ne_zero
  exact (pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) two_ne_zero).trans_lt hpow

theorem prefix_sup_middle (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.range (prefixMap (k := k) hd he) ⊔
      LinearMap.range (middleSection hd he h hH) = ⊤ :=
  (range_of_spanning (originalQuotient (k := k) hd he)
    (D.innerBinomial d e k (M.leftParity d) (M.rightParity d e k))
    (D.innerSection h (M.outer_parity hH) hH)
    (D.inner_decomposition h (M.outer_parity hH) hH).2).symm.trans
      (LinearMap.range_eq_top.mpr
        (RealInducedPairQuotientPresentation.quotient_surjective d e
          (M.leftParity d) (M.rightParity d e k) hd he))

/-- Exactness at the prefix is equivalent to the single remaining mixed-kernel containment. -/
theorem ker_eq_prefix_iff (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.ker (C.quotient hd he h hH) = LinearMap.range (prefixMap (k := k) hd he) ↔
      (LinearMap.ker (M.quotient hd he h hH)).map (middleSection hd he h hH) ≤
        LinearMap.range (prefixMap (k := k) hd he) := by
  rw [ker_quotient hd he h hH, sup_eq_left]

end RealInducedPairPositiveCrossedKernel

open RealStandardFiltration RealInducedPairLinkedReplacement
  RealInducedPairPositiveCrossedKernel in
/-- An actual prefix, exact mixed factorization and kernel decomposition for the positive quotient. -/
def RealInducedPairPositiveCrossedKernelStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k),
    ∃ (qW : KF 4 [.induced e, .induced d] →ₗ[ℂ] KF 4 [.induced d, .induced e])
      (qR : KF 4 (RealInducedPairDistantParity.outerPiece d e k
        (RealInducedPairCrossedMiddleQuotient.leftParity d)
        (RealInducedPairCrossedMiddleQuotient.rightParity d e k)) →ₗ[ℂ]
          KF 4 [.induced d, .induced e]),
      IsAdjacentPiece [] [] (.induced d) (.induced e)
        (RealInducedPairDistantParity.outerPiece d e k
          (RealInducedPairCrossedMiddleQuotient.leftParity d)
          (RealInducedPairCrossedMiddleQuotient.rightParity d e k)) ∧
      IsRealIntertwinerModulo 4 [.induced e, .induced d] [.induced d, .induced e] ⊥ qW ∧
      IsRealIntertwinerModulo 4
        (RealInducedPairDistantParity.outerPiece d e k
          (RealInducedPairCrossedMiddleQuotient.leftParity d)
          (RealInducedPairCrossedMiddleQuotient.rightParity d e k))
        [.induced d, .induced e] (LinearMap.range qW) qR ∧
      IsRealIntertwinerModulo 4 (RealInducedPairCrossedMiddleQuotient.middleList d e k)
        [.induced d, .induced e] (LinearMap.range qW ⊔ LinearMap.range qR)
        (middleSection hd he h hH) ∧
      LinearMap.ker (RealInducedPairPositiveCrossedQuotient.quotient hd he h hH) =
        (LinearMap.range qW ⊔ LinearMap.range qR) ⊔
          (LinearMap.ker (RealInducedPairCrossedMiddleQuotient.quotient hd he h hH)).map
            (middleSection hd he h hH) ∧
      (RealInducedPairPositiveCrossedQuotient.quotient hd he h hH).comp
        (middleSection hd he h hH) = RealInducedPairCrossedMiddleQuotient.quotient hd he h hH ∧
      (LinearMap.range qW ⊔ LinearMap.range qR) ⊔
        LinearMap.range (middleSection hd he h hH) = ⊤

theorem realInducedPairPositiveCrossedKernel : RealInducedPairPositiveCrossedKernelStatement := by
  intro d e k hd he h hH
  obtain ⟨qW, qR, hW, hR, hr⟩ :=
    RealInducedPairPositiveCrossedKernel.prefix_realization hd he h hH
  refine ⟨qW, qR, RealInducedPairPositiveCrossedKernel.outer_allowed h hH, hW, hR, ?_, ?_, ?_, ?_⟩
  · exact RealStandardFiltration.modulo_mono
      (RealInducedPairPositiveCrossedKernel.middleSection_modulo hd he h hH) (le_of_eq hr)
  · exact (RealInducedPairPositiveCrossedKernel.ker_quotient hd he h hH).trans
      (congrArg (fun N => N ⊔ _) hr)
  · exact RealInducedPairPositiveCrossedKernel.quotient_middleSection hd he h hH
  · exact (congrArg (fun N => N ⊔ _) hr).symm.trans
      (RealInducedPairPositiveCrossedKernel.prefix_sup_middle hd he h hH)

end Langlands.Archimedean
