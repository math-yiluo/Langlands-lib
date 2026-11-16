import Langlands.Representation.Archimedean.RealInducedPairQuotientPresentation
import Langlands.Representation.Archimedean.RealTailKernelReverse

/-! # Descending four ascending characters through two tail quotients -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairAscendingExchange

open RealBlockFrobeniusMap RealBlockMultiplier RealCharacterPair RealCharacterPairReducible
open RealStandardFiltration RealBlockPosition

/-- A recurrent swap intertwines exactly at the exponent difference of its source. -/
theorem swap_exact {n : ℕ} {pre post : List RealBlock} {c c' : RealCharacterData}
    {μ : ℤ → ℂ}
    (hn : realRank (pre ++ .character c :: .character c' :: post) = n)
    (hs : IsSymmetric (pairParity c c') (sigma0 c c') μ)
    (hr : IsRecurrent (c'.exponent - c.exponent + 1) (pairParity c c') μ) :
    IsRealIntertwinerModulo n (pre ++ dc c c' ++ post)
      (pre ++ .character c :: .character c' :: post) ⊥ (blockFrobMap (data_swap hn hs)) := by
  apply isRealIntertwinerModulo_blockFrobMap
  rw [exponent_swp_zero, exponent_swp_one]
  exact hr

namespace P
export RealInducedPairQuotientPresentation (lo hi positiveData X DX EX Z Xd Xe Dd De DeX DdEX
  dataDd dataDe dataDeX dataDdEX quotientMap quotientSection qd qe)
end P

variable (d e : ComplexCharacterData) (sd se : Fin 2)

abbrev X1 : List RealBlock := [.character (P.lo d sd), .character (P.lo e se),
  .character (P.hi d sd), .character (P.hi e se)]
abbrev X10 : List RealBlock := [.character (P.lo e se), .character (P.lo d sd),
  .character (P.hi d sd), .character (P.hi e se)]
abbrev X12 : List RealBlock := [.character (P.lo d sd), .character (P.lo e se),
  .character (P.hi e se), .character (P.hi d sd)]
abbrev X3 : List RealBlock := [.character (P.lo e se), .character (P.lo d sd),
  .character (P.hi e se), .character (P.hi d sd)]
abbrev MD : List RealBlock := [.character (P.lo e se), .induced (P.positiveData d sd),
  .character (P.hi e se)]
abbrev ME : List RealBlock := [.character (P.lo d sd), .induced (P.positiveData e se),
  .character (P.hi d sd)]

/-- The four independent actual multiplier data for the ascending exchange. -/
structure MultiplierData (μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ) : Prop where
  sym1 : IsSymmetric (pairParity (P.lo e se) (P.hi d sd))
    (sigma0 (P.lo e se) (P.hi d sd)) μ₁
  sym0 : IsSymmetric (pairParity (P.lo e se) (P.lo d sd))
    (sigma0 (P.lo e se) (P.lo d sd)) μ₀
  sym2 : IsSymmetric (pairParity (P.hi e se) (P.hi d sd))
    (sigma0 (P.hi e se) (P.hi d sd)) μ₂
  sym3 : IsSymmetric (pairParity (P.hi e se) (P.lo d sd))
    (sigma0 (P.hi e se) (P.lo d sd)) μ₃
  rec1 : IsRecurrent ((P.hi d sd).exponent - (P.lo e se).exponent + 1)
    (pairParity (P.lo e se) (P.hi d sd)) μ₁
  rec0 : IsRecurrent ((P.lo d sd).exponent - (P.lo e se).exponent + 1)
    (pairParity (P.lo e se) (P.lo d sd)) μ₀
  rec2 : IsRecurrent ((P.hi d sd).exponent - (P.hi e se).exponent + 1)
    (pairParity (P.hi e se) (P.hi d sd)) μ₂
  rec3 : IsRecurrent ((P.lo d sd).exponent - (P.hi e se).exponent + 1)
    (pairParity (P.hi e se) (P.lo d sd)) μ₃

namespace MultiplierData

variable {d e : ComplexCharacterData} {sd se : Fin 2} {μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ}
  (h : MultiplierData d e sd se μ₁ μ₀ μ₂ μ₃)

abbrev data1 := data_swap (n := 4) (pre := [.character (P.lo d sd)])
  (post := [.character (P.hi e se)]) rfl h.sym1
abbrev data0 := data_swap (n := 4) (pre := [])
  (post := [.character (P.hi d sd), .character (P.hi e se)]) rfl h.sym0
abbrev data20 := data_swap (n := 4)
  (pre := [.character (P.lo e se), .character (P.lo d sd)]) (post := []) rfl h.sym2
abbrev data21 := data_swap (n := 4)
  (pre := [.character (P.lo d sd), .character (P.lo e se)]) (post := []) rfl h.sym2
abbrev data02 := data_swap (n := 4) (pre := [])
  (post := [.character (P.hi e se), .character (P.hi d sd)]) rfl h.sym0
abbrev data3 := data_swap (n := 4) (pre := [.character (P.lo e se)])
  (post := [.character (P.hi d sd)]) rfl h.sym3

/-- Four crossings, before either target tail is applied. -/
def crossings : KF 4 (P.X d e sd se) →ₗ[ℂ] KF 4 (P.X e d se sd) :=
  (blockFrobMap h.data3).comp ((blockFrobMap h.data20).comp
    ((blockFrobMap h.data0).comp (blockFrobMap h.data1)))

theorem crossings_exact :
    IsRealIntertwinerModulo 4 (P.X d e sd se) (P.X e d se sd) ⊥ h.crossings :=
  modulo_comp_bot
    (swap_exact (n := 4) (pre := [.character (P.lo e se)])
      (post := [.character (P.hi d sd)]) rfl h.sym3 h.rec3)
    (modulo_comp_bot
      (swap_exact (n := 4) (pre := [.character (P.lo e se), .character (P.lo d sd)])
        (post := []) rfl h.sym2 h.rec2)
      (modulo_comp_bot
        (swap_exact (n := 4) (pre := [])
          (post := [.character (P.hi d sd), .character (P.hi e se)]) rfl h.sym0 h.rec0)
        (swap_exact (n := 4) (pre := [.character (P.lo d sd)])
          (post := [.character (P.hi e se)]) rfl h.sym1 h.rec1)))

theorem middle_comm (f : KF 4 (X1 d e sd se)) :
    blockFrobMap h.data20 (blockFrobMap h.data0 f) =
      blockFrobMap h.data02 (blockFrobMap h.data21 f) :=
  RealBlockFrobeniusDisjoint.blockFrobMap_disjoint_comm h.data0 h.data20 h.data21 h.data02
    (Or.inl (by change 1 < 2; omega)) f

variable (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)

abbrev dataMD := data_D (n := 4) (pre := [.character (P.lo e se)])
  (post := [.character (P.hi e se)]) rfl hd
  (RealInducedPairQuotientPresentation.pair_parity d sd)
  (RealInducedPairQuotientPresentation.hi_sub_lo d sd)
abbrev dataME := data_D (n := 4) (pre := [.character (P.lo d sd)])
  (post := [.character (P.hi d sd)]) rfl he
  (RealInducedPairQuotientPresentation.pair_parity e se)
  (RealInducedPairQuotientPresentation.hi_sub_lo e se)

/-- The d-tail kernel moves to the d-tail kernel at the other end. -/
theorem kernel_d (f : KF 4 (P.X d e sd se)) (hf : P.Dd d e sd se hd f = 0) :
    P.DeX e d se sd hd (h.crossings f) = 0 := by
  have hfirst : blockFrobMap (dataMD hd) (blockFrobMap h.data0 (blockFrobMap h.data1 f)) = 0 := by
    exact RealTailKernelInStages.kernel_step [] [.character (P.hi e se)]
      (P.lo e se) d sd rfl hd h.data0 h.data1 (P.dataDd d e sd se hd)
      (dataMD hd) h.rec0 h.rec1 f hf
  exact RealTailKernelInStages.kernel_step [.character (P.lo e se)] []
    (P.hi e se) d sd rfl hd h.data3 h.data20 (dataMD hd)
    (P.dataDeX e d se sd hd) h.rec3 h.rec2 _ hfirst

/-- The e-tail kernel moves to the e-tail kernel, using the other middle order. -/
theorem kernel_e (f : KF 4 (P.X d e sd se)) (hf : P.DeX d e sd se he f = 0) :
    P.Dd e d se sd he (h.crossings f) = 0 := by
  have hfirst : blockFrobMap (dataME he) (blockFrobMap h.data21 (blockFrobMap h.data1 f)) = 0 := by
    exact RealTailKernelReverse.kernel_step_inStages (P.hi d sd) e se
      [.character (P.lo d sd)] [] rfl he h.data1 h.data21 (P.dataDeX d e sd se he)
      (dataME he) h.rec1 h.rec2 f hf
  change P.Dd e d se sd he (blockFrobMap h.data3
    (blockFrobMap h.data20 (blockFrobMap h.data0 (blockFrobMap h.data1 f)))) = 0
  rw [h.middle_comm]
  exact RealTailKernelReverse.kernel_step_inStages (P.lo d sd) e se
    [] [.character (P.hi d sd)] rfl he h.data02 h.data3 (dataME he)
    (P.dataDd e d se sd he) h.rec0 h.rec3 _ hfirst

/-- Four crossings followed by the two actual target tails. -/
def beforeDescent : KF 4 (P.X d e sd se) →ₗ[ℂ] KF 4 [.induced e, .induced d] :=
  (P.quotientMap e d se sd he hd).comp h.crossings

theorem beforeDescent_exact :
    IsRealIntertwinerModulo 4 (P.X d e sd se) [.induced e, .induced d] ⊥
      (h.beforeDescent hd he) :=
  modulo_comp_bot (RealInducedPairQuotientPresentation.quotient_exact e d se sd he hd)
    h.crossings_exact

theorem kill_qd : (h.beforeDescent hd he).comp (P.qd d e sd se) = 0 := by
  ext f x
  have hf : P.Dd d e sd se hd (P.qd d e sd se f) = 0 :=
    RealInducedPairQuotientPresentation.tail_binomial_zero hd (pairParity_eq _ _)
      (RealInducedPairQuotientPresentation.pair_parity d sd) (neg_one_pow_sq_fin _)
      (RealInducedPairQuotientPresentation.dataQd d e sd se) (P.dataDd d e sd se hd) f
  have hk := h.kernel_d hd _ hf
  have ht : RealInducedPairQuotientPresentation.T e d se sd he hd
      (h.crossings (P.qd d e sd se f)) = 0 := by
    change P.De e d se sd hd (P.Dd e d se sd he _) = 0
    rw [RealInducedPairQuotientPresentation.tails_comm, hk, map_zero]
  exact congrArg (fun v : KF 4 (P.Z e d se sd) =>
    (ofEqMap (RealInducedPairQuotientPresentation.KF_Z e d se sd) v :
      Langlands.GeneralLinear 4 ℝ → ℂ) x) ht

theorem kill_qe : (h.beforeDescent hd he).comp (P.qe d e sd se) = 0 := by
  ext f x
  have hf : P.DeX d e sd se he (P.qe d e sd se f) = 0 :=
    RealInducedPairQuotientPresentation.tail_binomial_zero he (pairParity_eq _ _)
      (RealInducedPairQuotientPresentation.pair_parity e se) (neg_one_pow_sq_fin _)
      (RealInducedPairQuotientPresentation.dataQe d e sd se) (P.dataDeX d e sd se he) f
  have hk := h.kernel_e he _ hf
  have ht : RealInducedPairQuotientPresentation.T e d se sd he hd
      (h.crossings (P.qe d e sd se f)) = 0 := by
    change P.De e d se sd hd (P.Dd e d se sd he _) = 0
    rw [hk, map_zero]
  exact congrArg (fun v : KF 4 (P.Z e d se sd) =>
    (ofEqMap (RealInducedPairQuotientPresentation.KF_Z e d se sd) v :
      Langlands.GeneralLinear 4 ℝ → ℂ) x) ht

/-- The exchange on the actual two-induced-block modules. -/
def swap : KF 4 [.induced d, .induced e] →ₗ[ℂ] KF 4 [.induced e, .induced d] :=
  (h.beforeDescent hd he).comp (P.quotientSection d e sd se hd he)

/-- Exact quotient descent, its factorization identity and its unchanged range. -/
theorem swap_descend :
    IsRealIntertwinerModulo 4 [.induced d, .induced e] [.induced e, .induced d] ⊥
      (h.swap hd he) ∧
    (h.swap hd he).comp (P.quotientMap d e sd se hd he) = h.beforeDescent hd he ∧
    LinearMap.range (h.swap hd he) = LinearMap.range (h.beforeDescent hd he) :=
  RealInducedPairQuotientPresentation.descend d e sd se hd he
    (h.beforeDescent hd he) (h.beforeDescent_exact hd he) (h.kill_qd hd he) (h.kill_qe hd he)

end MultiplierData
end RealInducedPairAscendingExchange

open RealInducedPairAscendingExchange RealStandardFiltration in
/-- Four recurrent ascending-character swaps descend to an exact exchange of two
positive-weight induction blocks, with the prescribed factorization and range. -/
def RealInducedPairAscendingExchangeStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (sd se : Fin 2)
    (μ₁ μ₀ μ₂ μ₃ : ℤ → ℂ)
    (h : MultiplierData d e sd se μ₁ μ₀ μ₂ μ₃)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs),
    IsRealIntertwinerModulo 4 [.induced d, .induced e] [.induced e, .induced d] ⊥
      (h.swap hd he) ∧
    (h.swap hd he).comp (P.quotientMap d e sd se hd he) = h.beforeDescent hd he ∧
    LinearMap.range (h.swap hd he) = LinearMap.range (h.beforeDescent hd he)

open RealInducedPairAscendingExchange in
theorem realInducedPairAscendingExchange : RealInducedPairAscendingExchangeStatement := by
  intro d e sd se μ₁ μ₀ μ₂ μ₃ h hd he
  exact h.swap_descend hd he

end Langlands.Archimedean
