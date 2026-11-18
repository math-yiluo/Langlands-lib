import Langlands.Representation.Archimedean.RealInducedPairPositiveCrossedKernel
import Langlands.Representation.Archimedean.RealInducedPairPositiveOppositeOuter
import Langlands.Representation.Archimedean.RealStandardFiltrationQuotientDescent

/-! # The two outer parity prefixes in the positive-inner filtration -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealInducedPairPositiveTwoPrefix

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealInducedPairAscendingExchange
  RealInducedPairLinkedReplacement RealInducedPairCrossedReplacement RealCharacterPair

namespace K
export RealInducedPairPositiveCrossedKernel (realize_prefix prefixMap middleSection
  prefix_realization prefix_sup_middle middleSection_modulo)
end K

namespace M
export RealInducedPairCrossedMiddleQuotient (leftParity rightParity middleList quotient
  quotient_exact quotient_surjective outer_parity)
end M

namespace D
export RealInducedPairDistantParity (outerPiece innerBinomial middle outerSection
  outerBinomial exists_ascendingData outer_decomposition middle_exact middle_surjective
  beforeDescent_eq innerBinomial_exact)
end D

namespace O
export RealInducedPairPositiveOppositeOuter (flipParity oppositeOuter opposite_outer_parity
  opposite_allowed)
end O

variable {d e : ComplexCharacterData} {k : ℕ}

def parityPrefix (sd se : Fin 2) (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    KF 4 (X1 d e sd se) →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  (P.quotientMap d e sd se hd he).comp (D.innerBinomial d e k sd se)

theorem prefix_realization (sd se : Fin 2)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (hp : Even ((outerWeight d e k : ℤ) - 1 - pairParity (P.lo d sd) (P.hi e se))) :
    ∃ (qW : KF 4 [.induced e, .induced d] →ₗ[ℂ] KF 4 [.induced d, .induced e])
      (qR : KF 4 (D.outerPiece d e k sd se) →ₗ[ℂ] KF 4 [.induced d, .induced e]),
      IsRealIntertwinerModulo 4 [.induced e, .induced d] [.induced d, .induced e] ⊥ qW ∧
      IsRealIntertwinerModulo 4 (D.outerPiece d e k sd se)
        [.induced d, .induced e] (LinearMap.range qW) qR ∧
      LinearMap.range (parityPrefix (k := k) sd se hd he) =
        LinearMap.range qW ⊔ LinearMap.range qR := by
  obtain ⟨μ₀, μ₂, hm, hn0, hn2⟩ := D.exists_ascendingData h hp hH
  obtain ⟨hq, _, hrange⟩ := hm.swap_descend he hd
  let F := (D.middle hm).comp (D.outerBinomial d e k sd se)
  let s := (D.middle hm).comp (D.outerSection h hp)
  have hword : hm.beforeDescent he hd = (parityPrefix (k := k) sd se hd he).comp F :=
    (D.beforeDescent_eq hm hd he).trans
      (LinearMap.comp_assoc F (D.innerBinomial d e k sd se) (P.quotientMap d e sd se hd he)).symm
  have hr : LinearMap.range (hm.swap he hd) =
      LinearMap.range ((parityPrefix (k := k) sd se hd he).comp F) :=
    hrange.trans (congrArg LinearMap.range hword)
  have hs := RealInducedPairDistantFiltration.modulo_comp_range
    (D.middle_exact hm) (D.outer_decomposition h hp).1
  have hspan := RealInducedPairDistantFiltration.span_comp (D.middle hm) _ _
    (D.middle_surjective hm hn0 hn2) (D.outer_decomposition h hp).2
  have hprefix : IsRealIntertwinerModulo 4 (X1 d e sd se) [.induced d, .induced e] ⊥
      (parityPrefix (k := k) sd se hd he) :=
    modulo_comp_bot
      (RealInducedPairQuotientPresentation.quotient_exact d e sd se hd he)
      (D.innerBinomial_exact h hp hH)
  have hh := K.realize_prefix (parityPrefix (k := k) sd se hd he) F s (hm.swap he hd)
    hprefix hs hr hspan
  exact ⟨hm.swap he hd, (parityPrefix (k := k) sd se hd he).comp s, hq, hh⟩

def oppositePrefix (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :=
  parityPrefix (k := k) (O.flipParity (M.leftParity d)) (O.flipParity (M.rightParity d e k)) hd he

def totalPrefix (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    Submodule ℂ (KF 4 [.induced d, .induced e]) :=
  LinearMap.range (K.prefixMap (k := k) hd he) ⊔
    LinearMap.range (oppositePrefix (k := k) hd he)

/-- The remaining containment is into both outer parity prefixes together. -/
def Absorption (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) : Prop :=
  (LinearMap.ker (M.quotient hd he h hH)).map (K.middleSection hd he h hH) ≤
    totalPrefix (k := k) hd he

theorem absorption_iff_ker_le (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    Absorption hd he h hH ↔
      LinearMap.ker (RealInducedPairPositiveCrossedQuotient.quotient hd he h hH) ≤
        totalPrefix (k := k) hd he := by
  rw [RealInducedPairPositiveCrossedKernel.ker_quotient hd he h hH, sup_le_iff]
  exact ⟨fun hA => ⟨le_sup_left, hA⟩, fun hA => hA.2⟩

section Assembly

variable {n : ℕ} {V W R S C : List RealBlock} {P : List RealBlock → Prop}

theorem five_piece
    (q0 q2 : KF n W →ₗ[ℂ] KF n V) (q1 : KF n R →ₗ[ℂ] KF n V)
    (q3 : KF n S →ₗ[ℂ] KF n V) (q4 : KF n C →ₗ[ℂ] KF n V)
    (h0 : IsRealIntertwinerModulo n W V ⊥ q0)
    (h1 : IsRealIntertwinerModulo n R V (LinearMap.range q0) q1)
    (h2 : IsRealIntertwinerModulo n W V ⊥ q2)
    (h3 : IsRealIntertwinerModulo n S V (LinearMap.range q2) q3)
    (h4 : IsRealIntertwinerModulo n C V
      ((LinearMap.range q0 ⊔ LinearMap.range q1) ⊔
        (LinearMap.range q2 ⊔ LinearMap.range q3)) q4)
    (hspan : ((LinearMap.range q0 ⊔ LinearMap.range q1) ⊔
        (LinearMap.range q2 ⊔ LinearMap.range q3)) ⊔ LinearMap.range q4 = ⊤)
    (hW : P W) (hR : P R) (hS : P S) (hC : P C) : HasFiltration n V P := by
  let es : Fin 5 → List RealBlock := ![W, R, W, S, C]
  let qs : ∀ j : Fin 5, KF n (es j) →ₗ[ℂ] KF n V :=
    Fin.cons (α := fun j : Fin 5 => KF n (es j) →ₗ[ℂ] KF n V)
      q0 (Fin.cons q1 (Fin.cons q2 (Fin.cons q3 (Fin.cons q4 finZeroElim))))
  have hprefix :
      (LinearMap.range q0 ⊔ LinearMap.range q1) ⊔
          (LinearMap.range q2 ⊔ LinearMap.range q3) ≤
        ⨆ (i : Fin 5) (_ : i < 4), LinearMap.range (qs i) := by
    apply sup_le
    · apply sup_le
      · exact le_iSup₂_of_le (f := fun (i : Fin 5) (_ : i < 4) => LinearMap.range (qs i))
          0 (by decide) le_rfl
      · exact le_iSup₂_of_le (f := fun (i : Fin 5) (_ : i < 4) => LinearMap.range (qs i))
          1 (by decide) le_rfl
    · apply sup_le
      · exact le_iSup₂_of_le (f := fun (i : Fin 5) (_ : i < 4) => LinearMap.range (qs i))
          2 (by decide) le_rfl
      · exact le_iSup₂_of_le (f := fun (i : Fin 5) (_ : i < 4) => LinearMap.range (qs i))
          3 (by decide) le_rfl
  refine ⟨Fin 5, inferInstance, inferInstance, es, qs, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hW
    · exact hR
    · exact hW
    · exact hS
    · exact hC
  · intro i
    fin_cases i
    · exact modulo_mono h0 bot_le
    · exact modulo_mono h1
        (le_iSup₂_of_le (f := fun (i : Fin 5) (_ : i < 1) => LinearMap.range (qs i))
          0 (by decide) le_rfl)
    · exact modulo_mono h2 bot_le
    · exact modulo_mono h3
        (le_iSup₂_of_le (f := fun (i : Fin 5) (_ : i < 3) => LinearMap.range (qs i))
          2 (by decide) le_rfl)
    · exact modulo_mono h4 hprefix
  · apply eq_top_iff.mpr
    rw [← hspan]
    apply sup_le
    · exact hprefix.trans (iSup₂_le fun i _ => le_iSup (fun i => LinearMap.range (qs i)) i)
    · exact le_iSup_of_le (4 : Fin 5) le_rfl

end Assembly

theorem filtration (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k)
    (habs : Absorption hd he h hH) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  obtain ⟨q0, q1, h0, h1, heq0⟩ := K.prefix_realization hd he h hH
  obtain ⟨q2, q3, h2, h3, heq1⟩ :=
    prefix_realization (O.flipParity (M.leftParity d)) (O.flipParity (M.rightParity d e k))
      hd he h hH (O.opposite_outer_parity hH)
  have hT := modulo_mono (K.middleSection_modulo hd he h hH)
    (le_sup_left : LinearMap.range (K.prefixMap (k := k) hd he) ≤ totalPrefix (k := k) hd he)
  obtain ⟨q4, h4, hrange⟩ := exists_quotient_descent hT (M.quotient_exact hd he h hH)
    (M.quotient_surjective hd he h hH) habs
  change IsRealIntertwinerModulo 4 (crossedPair d e k) [.induced d, .induced e]
    (totalPrefix (k := k) hd he) q4 at h4
  change totalPrefix (k := k) hd he ⊔ LinearMap.range q4 =
    totalPrefix (k := k) hd he ⊔ LinearMap.range (K.middleSection hd he h hH) at hrange
  have hspan : totalPrefix (k := k) hd he ⊔ LinearMap.range q4 = ⊤ := by
    rw [hrange]
    apply eq_top_iff.mpr
    rw [← K.prefix_sup_middle hd he h hH]
    exact sup_le_sup
      (le_sup_left : LinearMap.range (K.prefixMap (k := k) hd he) ≤ totalPrefix (k := k) hd he)
      le_rfl
  have heq : totalPrefix (k := k) hd he =
      (LinearMap.range q0 ⊔ LinearMap.range q1) ⊔
        (LinearMap.range q2 ⊔ LinearMap.range q3) := by
    unfold totalPrefix
    rw [heq0]
    exact congrArg (fun Z => (LinearMap.range q0 ⊔ LinearMap.range q1) ⊔ Z) heq1
  rw [heq] at h4 hspan
  apply (realAdjacentFiltration_iff 4 [] [] (.induced d) (.induced e)).mpr
  exact five_piece q0 q2 q1 q3 q4 h0 h1 h2 h3 h4 hspan
    ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩
    (RealInducedPairPositiveCrossedKernel.outer_allowed h hH)
    (O.opposite_allowed h hH)
    (by simpa using RealInducedPairCrossedReplacement.isAdjacentPiece [] [] h hH)

end Langlands.Archimedean.RealInducedPairPositiveTwoPrefix

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement
  RealInducedPairPositiveTwoPrefix

/-- The positive-inner filtration follows from absorption into the two explicit parity prefixes. -/
def RealInducedPairPositiveTwoPrefixStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k),
    Absorption hd he h hH → RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairPositiveTwoPrefix : RealInducedPairPositiveTwoPrefixStatement :=
  fun _ _ _ hd he h hH hA => filtration hd he h hH hA

end Langlands.Archimedean
