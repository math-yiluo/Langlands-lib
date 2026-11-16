import Langlands.Representation.Archimedean.RealCharacterPairReducible
import Langlands.Representation.Archimedean.RealCharacterInducedPushforward
import Langlands.Representation.Archimedean.RealStandardFiltration
import Langlands.Representation.Archimedean.RealBlockFrobeniusDisjoint

/-! # Ascending-character quotients for two real induction blocks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairQuotientPresentation

open RealBlockFrobeniusMap RealBlockMultiplier RealBlockJacquet RealBlockPosition
open RealCharacterPair RealCharacterPairReducible RealStandardFiltration
open RealBlockFrobeniusDisjoint

section General

variable {n p : ℕ} {ds es fs : List RealBlock} {ε : ℤ}

/-- The two multiplier supports are disjoint on the source parity class. -/
theorem tail_binomial_zero {ℓ : ℕ} (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {σ τ : ℂ} (hτ : τ ^ 2 = 1)
    (hq : IsBlockFrobData n ds es p ε σ (binomialMultiplier ℓ ε))
    (hD : IsBlockFrobData n es fs p ε τ (tailMultiplier ℓ ε τ))
    (f : KF n ds) : blockFrobMap hD (blockFrobMap hq f) = 0 := by
  refine eq_of_blockFourierCoefficient_eq hD.lt fun j k hk => ?_
  rw [blockFourierCoefficient_blockFrobMap hD _ hk,
    blockFourierCoefficient_blockFrobMap hq _ hk]
  change _ = blockFourierCoefficient n p j (0 : Langlands.GeneralLinear n ℝ → ℂ) k
  rw [blockFourierCoefficient_zero]
  by_cases hj : Even (j - ε)
  · by_cases hb : binomialMultiplier ℓ ε j = 0
    · rw [hb, zero_mul, mul_zero]
    · have hjl := (binomialMultiplier_ne_zero_iff hℓ hε hpar hj).mp hb
      have ht : tailMultiplier ℓ ε τ j = 0 := by
        by_contra ht
        have := (tailMultiplier_ne_zero_iff hℓ hε hpar hτ hj).mp ht
        omega
      rw [ht, zero_mul]
  · rw [blockFourierCoefficient_eq_zero_of_not_even hq.lt hq.par f hj k,
      mul_zero, mul_zero]

/-- The tail kernel is exactly the binomial image, with both maps constructed by Frobenius. -/
theorem ker_tail_eq_range {ℓ : ℕ} (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {σ σ' τ : ℂ} (hτ : τ ^ 2 = 1)
    (hq : IsBlockFrobData n ds es p ε σ (binomialMultiplier ℓ ε))
    (hB : IsBlockFrobData n es ds p ε σ' (fun j => (binomialMultiplier ℓ ε j)⁻¹))
    (hD : IsBlockFrobData n es fs p ε τ (tailMultiplier ℓ ε τ)) :
    LinearMap.ker (blockFrobMap hD) = LinearMap.range (blockFrobMap hq) := by
  apply le_antisymm
  · refine ker_le_range hq hB hD fun j hj hne => ?_
    have hb : binomialMultiplier ℓ ε j = 0 := by
      by_contra hb
      exact hne (mul_inv_cancel₀ hb)
    have hjl : ¬ |j| < ℓ := fun hlt =>
      (binomialMultiplier_ne_zero_iff hℓ hε hpar hj).mpr hlt hb
    refine (tailMultiplier_ne_zero_iff hℓ hε hpar hτ hj).mpr ?_
    rcases (not_lt.mp hjl).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd heq.le (not_le.mpr (abs_lt_of_parity hpar hj heq.symm.le))
  · rintro _ ⟨f, rfl⟩
    exact tail_binomial_zero hℓ hε hpar hτ hq hD f

/-- The ascending tail is an exact intertwiner in arbitrary surrounding lists. -/
theorem tail_exact {pre post : List RealBlock} {c c' : RealCharacterData} {ℓ : ℕ}
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character c' :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c c'))
    (hν : c'.exponent - c.exponent = ℓ) :
    IsRealIntertwinerModulo n (pre ++ RealBlock.character c :: RealBlock.character c' :: post)
      (pre ++ indBlock c c' ℓ ++ post) ⊥ (blockFrobMap (data_D hn hℓ hpar hν)) := by
  apply isRealIntertwinerModulo_blockFrobMap
  have h0 : GramFormula.realPositionExponent
      (pre ++ RealBlock.character c :: RealBlock.character c' :: post) (realRank pre) =
        c.exponent := by
    rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character c'),
      exponent_mid_zero pre post (realRank_cd (c := c) (d := c') ▸ two_pos)]
    rfl
  have h1 : GramFormula.realPositionExponent
      (pre ++ RealBlock.character c :: RealBlock.character c' :: post) (realRank pre + 1) =
        c'.exponent := by
    rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character c'),
      exponent_mid_one pre post (realRank_cd (c := c) (d := c') ▸ one_lt_two)]
    rfl
  rw [h0, h1, show c.exponent - c'.exponent + 1 = 1 - (ℓ : ℂ) by
    linear_combination -hν]
  exact isRecurrent_tailMultiplier hℓ (pairParity_eq c c') hpar (neg_one_pow_sq_fin _)

/-- The reversed-pair binomial map is an exact intertwiner. -/
theorem binomial_exact {pre post : List RealBlock} {c c' : RealCharacterData} {ℓ : ℕ}
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character c' :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c c'))
    (hν : c'.exponent - c.exponent = ℓ) :
    IsRealIntertwinerModulo n (pre ++ dc c c' ++ post)
      (pre ++ RealBlock.character c :: RealBlock.character c' :: post) ⊥
      (blockFrobMap (data_q0 (ℓ := ℓ) hn)) := by
  apply isRealIntertwinerModulo_blockFrobMap
  rw [exponent_swp_zero, exponent_swp_one, hν]
  exact isRecurrent_binomialMultiplier hℓ (pairParity_eq c c') hpar

/-- Transport a split surjection across equality of its target function spaces. -/
theorem transport_section {a b c : List RealBlock} (h : KF n b = KF n c)
    (T : KF n a →ₗ[ℂ] KF n b) (S : KF n b →ₗ[ℂ] KF n a)
    (hTS : ∀ f, T (S f) = f) (f : KF n c) :
    ((ofEqMap h).comp T) ((S.comp (ofEqMap h.symm)) f) = f := by
  change ofEqMap h (T (S (ofEqMap h.symm f))) = f
  rw [hTS]
  apply Subtype.ext
  rfl

end General

/-! ## The ascending pair for one induction block -/

/-- The lower character, with freely chosen parity. -/
def lo (d : ComplexCharacterData) (s : Fin 2) : RealCharacterData :=
  RealJacquetFrobenius.charData s (d.exponent - (d.weight.natAbs : ℂ) / 2)

/-- The upper character; its parity makes the pair reducible at the required weight. -/
def hi (d : ComplexCharacterData) (s : Fin 2) : RealCharacterData :=
  RealJacquetFrobenius.charData
    ⟨(s.val + d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩
    (d.exponent + (d.weight.natAbs : ℂ) / 2)

abbrev positiveData (d : ComplexCharacterData) (s : Fin 2) : ComplexCharacterData :=
  pairInduced (lo d s) (hi d s) d.weight.natAbs

theorem hi_sub_lo (d : ComplexCharacterData) (s : Fin 2) :
    (hi d s).exponent - (lo d s).exponent = (d.weight.natAbs : ℂ) := by
  change (d.exponent + (d.weight.natAbs : ℂ) / 2) -
    (d.exponent - (d.weight.natAbs : ℂ) / 2) = _
  ring

theorem pair_parity (d : ComplexCharacterData) (s : Fin 2) :
    Even ((d.weight.natAbs : ℤ) - 1 - pairParity (lo d s) (hi d s)) := by
  unfold pairParity
  change Even ((d.weight.natAbs : ℤ) - 1 -
    (((s.val + (s.val + d.weight.natAbs + 1) % 2) % 2 : ℕ) : ℤ))
  rw [Int.even_iff]
  omega

@[simp] theorem positiveData_weight (d : ComplexCharacterData) (s : Fin 2) :
    (positiveData d s).weight = (d.weight.natAbs : ℤ) := rfl

@[simp] theorem positiveData_exponent (d : ComplexCharacterData) (s : Fin 2) :
    (positiveData d s).exponent = d.exponent := by
  change ((d.exponent - (d.weight.natAbs : ℂ) / 2) +
    (d.exponent + (d.weight.natAbs : ℂ) / 2)) / 2 = _
  ring

/-! ## The four-character square -/

variable (d e : ComplexCharacterData) (sd se : Fin 2)

abbrev X : List RealBlock := [.character (lo d sd), .character (hi d sd),
  .character (lo e se), .character (hi e se)]
abbrev DX : List RealBlock := [.induced (positiveData d sd),
  .character (lo e se), .character (hi e se)]
abbrev EX : List RealBlock := [.character (lo d sd), .character (hi d sd),
  .induced (positiveData e se)]
abbrev Z : List RealBlock := [.induced (positiveData d sd), .induced (positiveData e se)]
abbrev Xd : List RealBlock := [.character (hi d sd), .character (lo d sd),
  .character (lo e se), .character (hi e se)]
abbrev Xe : List RealBlock := [.character (lo d sd), .character (hi d sd),
  .character (hi e se), .character (lo e se)]
abbrev DXe : List RealBlock := [.induced (positiveData d sd),
  .character (hi e se), .character (lo e se)]

/-- Tail data for the left pair, before collapsing the right pair. -/
abbrev dataDd (hd : 0 < d.weight.natAbs) :=
  data_D (n := 4) (pre := [])
    (post := [.character (lo e se), .character (hi e se)]) rfl hd (pair_parity d sd)
    (hi_sub_lo d sd)

abbrev dataSd (hd : 0 < d.weight.natAbs) :=
  data_q1 (n := 4) (pre := [])
    (post := [.character (lo e se), .character (hi e se)]) rfl hd (pair_parity d sd)
    (hi_sub_lo d sd)

/-- Tail data for the right pair, after collapsing the left pair. -/
abbrev dataDe (he : 0 < e.weight.natAbs) :=
  data_D (n := 4) (pre := [.induced (positiveData d sd)]) (post := [])
    rfl he (pair_parity e se) (hi_sub_lo e se)

abbrev dataSe (he : 0 < e.weight.natAbs) :=
  data_q1 (n := 4) (pre := [.induced (positiveData d sd)]) (post := [])
    rfl he (pair_parity e se) (hi_sub_lo e se)

abbrev dataDeX (he : 0 < e.weight.natAbs) :=
  data_D (n := 4) (pre := [.character (lo d sd), .character (hi d sd)]) (post := [])
    rfl he (pair_parity e se) (hi_sub_lo e se)

abbrev dataDdEX (hd : 0 < d.weight.natAbs) :=
  data_D (n := 4) (pre := []) (post := [.induced (positiveData e se)])
    rfl hd (pair_parity d sd) (hi_sub_lo d sd)

abbrev dataQd := data_q0 (n := 4) (ℓ := d.weight.natAbs) (pre := [])
  (post := [.character (lo e se), .character (hi e se)]) (c := lo d sd) (d := hi d sd) rfl

abbrev dataBd := data_B (n := 4) (ℓ := d.weight.natAbs) (pre := [])
  (post := [.character (lo e se), .character (hi e se)]) (c := lo d sd) (d := hi d sd) rfl

abbrev dataQe := data_q0 (n := 4) (ℓ := e.weight.natAbs)
  (pre := [.character (lo d sd), .character (hi d sd)]) (post := [])
  (c := lo e se) (d := hi e se) rfl

abbrev dataQeD := data_q0 (n := 4) (ℓ := e.weight.natAbs)
  (pre := [.induced (positiveData d sd)]) (post := []) (c := lo e se) (d := hi e se) rfl

abbrev dataBeD := data_B (n := 4) (ℓ := e.weight.natAbs)
  (pre := [.induced (positiveData d sd)]) (post := []) (c := lo e se) (d := hi e se) rfl

abbrev dataSdXe (hd : 0 < d.weight.natAbs) :=
  data_q1 (n := 4) (pre := [])
    (post := [.character (hi e se), .character (lo e se)]) rfl hd (pair_parity d sd)
    (hi_sub_lo d sd)

def Dd (hd : 0 < d.weight.natAbs) : KF 4 (X d e sd se) →ₗ[ℂ] KF 4 (DX d e sd se) :=
  blockFrobMap (dataDd d e sd se hd)
def Sd (hd : 0 < d.weight.natAbs) : KF 4 (DX d e sd se) →ₗ[ℂ] KF 4 (X d e sd se) :=
  blockFrobMap (dataSd d e sd se hd)
def De (he : 0 < e.weight.natAbs) : KF 4 (DX d e sd se) →ₗ[ℂ] KF 4 (Z d e sd se) :=
  blockFrobMap (dataDe d e sd se he)
def Se (he : 0 < e.weight.natAbs) : KF 4 (Z d e sd se) →ₗ[ℂ] KF 4 (DX d e sd se) :=
  blockFrobMap (dataSe d e sd se he)
def DeX (he : 0 < e.weight.natAbs) : KF 4 (X d e sd se) →ₗ[ℂ] KF 4 (EX d e sd se) :=
  blockFrobMap (dataDeX d e sd se he)
def DdEX (hd : 0 < d.weight.natAbs) : KF 4 (EX d e sd se) →ₗ[ℂ] KF 4 (Z d e sd se) :=
  blockFrobMap (dataDdEX d e sd se hd)
def qd : KF 4 (Xd d e sd se) →ₗ[ℂ] KF 4 (X d e sd se) :=
  blockFrobMap (dataQd d e sd se)
def qe : KF 4 (Xe d e sd se) →ₗ[ℂ] KF 4 (X d e sd se) :=
  blockFrobMap (dataQe d e sd se)
def qeD : KF 4 (DXe d e sd se) →ₗ[ℂ] KF 4 (DX d e sd se) :=
  blockFrobMap (dataQeD d e sd se)
def SdXe (hd : 0 < d.weight.natAbs) : KF 4 (DXe d e sd se) →ₗ[ℂ] KF 4 (Xe d e sd se) :=
  blockFrobMap (dataSdXe d e sd se hd)

variable (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)

theorem Dd_Sd (f : KF 4 (DX d e sd se)) : Dd d e sd se hd (Sd d e sd se hd f) = f :=
  RealCharacterInducedPushforward.tail_inv hd (pairParity_eq _ _) (pair_parity d sd) (neg_one_pow_sq_fin _)
    (dataDd d e sd se hd) (dataSd d e sd se hd) rfl
    (by rw [positiveData_weight, abs_of_nonneg (Int.natCast_nonneg _)]) f

theorem De_Se (f : KF 4 (Z d e sd se)) : De d e sd se he (Se d e sd se he f) = f :=
  RealCharacterInducedPushforward.tail_inv he (pairParity_eq _ _) (pair_parity e se) (neg_one_pow_sq_fin _)
    (dataDe d e sd se he) (dataSe d e sd se he) rfl
    (by rw [positiveData_weight, abs_of_nonneg (Int.natCast_nonneg _)]) f

theorem ker_Dd : LinearMap.ker (Dd d e sd se hd) = LinearMap.range (qd d e sd se) :=
  ker_tail_eq_range hd (pairParity_eq _ _) (pair_parity d sd) (neg_one_pow_sq_fin _)
    (dataQd d e sd se) (dataBd d e sd se) (dataDd d e sd se hd)

theorem ker_De : LinearMap.ker (De d e sd se he) = LinearMap.range (qeD d e sd se) :=
  ker_tail_eq_range he (pairParity_eq _ _) (pair_parity e se) (neg_one_pow_sq_fin _)
    (dataQeD d e sd se) (dataBeD d e sd se) (dataDe d e sd se he)

theorem tails_comm (f : KF 4 (X d e sd se)) :
    De d e sd se he (Dd d e sd se hd f) = DdEX d e sd se hd (DeX d e sd se he f) :=
  blockFrobMap_disjoint_comm (dataDd d e sd se hd) (dataDe d e sd se he)
    (dataDeX d e sd se he) (dataDdEX d e sd se hd) (Or.inl (by change 1 < 2; omega)) f

theorem section_low_comm (f : KF 4 (DXe d e sd se)) :
    qe d e sd se (SdXe d e sd se hd f) = Sd d e sd se hd (qeD d e sd se f) :=
  blockFrobMap_disjoint_comm (dataSdXe d e sd se hd) (dataQe d e sd se)
    (dataQeD d e sd se) (dataSd d e sd se hd) (Or.inl (by change 1 < 2; omega)) f

include hd in
theorem qd_exact : IsRealIntertwinerModulo 4 (Xd d e sd se) (X d e sd se) ⊥
    (qd d e sd se) :=
  binomial_exact (pre := []) (post := [.character (lo e se), .character (hi e se)])
    rfl hd (pair_parity d sd) (hi_sub_lo d sd)

include he in
theorem qe_exact : IsRealIntertwinerModulo 4 (Xe d e sd se) (X d e sd se) ⊥
    (qe d e sd se) :=
  binomial_exact (pre := [.character (lo d sd), .character (hi d sd)]) (post := [])
    rfl he (pair_parity e se) (hi_sub_lo e se)

/-- Collapse both ascending pairs. -/
def T : KF 4 (X d e sd se) →ₗ[ℂ] KF 4 (Z d e sd se) :=
  (De d e sd se he).comp (Dd d e sd se hd)

/-- A linear section, without any claim of exact intertwining. -/
def S : KF 4 (Z d e sd se) →ₗ[ℂ] KF 4 (X d e sd se) :=
  (Sd d e sd se hd).comp (Se d e sd se he)

theorem T_S (f : KF 4 (Z d e sd se)) : T d e sd se hd he (S d e sd se hd he f) = f := by
  change De d e sd se he (Dd d e sd se hd (Sd d e sd se hd (Se d e sd se he f))) = f
  rw [Dd_Sd, De_Se]

theorem T_surjective : Function.Surjective (T d e sd se hd he) :=
  fun f => ⟨S d e sd se hd he f, T_S d e sd se hd he f⟩

theorem Dd_exact : IsRealIntertwinerModulo 4 (X d e sd se) (DX d e sd se) ⊥
    (Dd d e sd se hd) :=
  tail_exact (pre := []) (post := [.character (lo e se), .character (hi e se)])
    rfl hd (pair_parity d sd) (hi_sub_lo d sd)

theorem De_exact : IsRealIntertwinerModulo 4 (DX d e sd se) (Z d e sd se) ⊥
    (De d e sd se he) :=
  tail_exact (pre := [.induced (positiveData d sd)]) (post := [])
    rfl he (pair_parity e se) (hi_sub_lo e se)

theorem T_exact : IsRealIntertwinerModulo 4 (X d e sd se) (Z d e sd se) ⊥
    (T d e sd se hd he) :=
  modulo_comp_bot (De_exact d e sd se he) (Dd_exact d e sd se hd)

/-- The composite kernel has two explicit full-character low-mode generators. -/
theorem ker_T : LinearMap.ker (T d e sd se hd he) =
    LinearMap.range (qd d e sd se) ⊔ LinearMap.range (qe d e sd se) := by
  apply le_antisymm
  · intro f hf
    have hDdf : Dd d e sd se hd f ∈ LinearMap.ker (De d e sd se he) := hf
    rw [ker_De d e sd se he] at hDdf
    obtain ⟨b, hb⟩ := hDdf
    have hr : f - Sd d e sd se hd (Dd d e sd se hd f) ∈
        LinearMap.ker (Dd d e sd se hd) := by
      rw [LinearMap.mem_ker, map_sub, Dd_Sd, sub_self]
    rw [ker_Dd d e sd se hd] at hr
    obtain ⟨a, ha⟩ := hr
    have hf' : f = qd d e sd se a + qe d e sd se (SdXe d e sd se hd b) := by
      rw [section_low_comm d e sd se hd, hb, ha]
      abel
    rw [hf']
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a, rfl⟩)
      (Submodule.mem_sup_right ⟨SdXe d e sd se hd b, rfl⟩)
  · apply sup_le
    · rintro _ ⟨a, rfl⟩
      change De d e sd se he (Dd d e sd se hd (qd d e sd se a)) = 0
      have ha : qd d e sd se a ∈ LinearMap.ker (Dd d e sd se hd) := by
        rw [ker_Dd d e sd se hd]
        exact ⟨a, rfl⟩
      rw [show Dd d e sd se hd (qd d e sd se a) = 0 from ha, map_zero]
    · rintro _ ⟨b, rfl⟩
      change De d e sd se he (Dd d e sd se hd (qe d e sd se b)) = 0
      rw [tails_comm d e sd se hd he]
      have hb : DeX d e sd se he (qe d e sd se b) = 0 :=
        tail_binomial_zero he (pairParity_eq _ _) (pair_parity e se)
          (neg_one_pow_sq_fin _) (dataQe d e sd se) (dataDeX d e sd se he) b
      rw [hb, map_zero]

/-! ## Identify the quotient with the original induction data -/

/-- The two actual induction conditions, at positions zero and two. -/
theorem mem_induced_pair_iff (n : ℕ) (d e : ComplexCharacterData)
    (f : Langlands.GeneralLinear n ℝ → ℂ) :
    f ∈ realStandardModule n [.induced d, .induced e] ↔
      f ∈ principalSeries ℝ n (realPositionCharacter [.induced d, .induced e]) ∧
      (∀ j : ℤ, |j| < |d.weight| → ∀ g, blockFourierCoefficient n 0 j f g = 0) ∧
      (∀ j : ℤ, |j| < |e.weight| → ∀ g, blockFourierCoefficient n 2 j f g = 0) := by
  rw [mem_realStandardModule_iff]
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨hf, h 0 d rfl, h 2 e rfl⟩
  · rintro ⟨hf, hd, he⟩
    refine ⟨hf, fun p dI hI => ?_⟩
    rcases p with _ | _ | _ | _ | p
    · simp only [realInducedBlockAt, Option.some.injEq] at hI
      subst dI
      exact hd
    · simp [realInducedBlockAt] at hI
    · simp only [realInducedBlockAt, Option.some.injEq] at hI
      subst dI
      exact he
    · simp [realInducedBlockAt] at hI
    · simp [realInducedBlockAt] at hI

/-- Absolute weight and exponent identify the quotient standard module with the original. -/
theorem standardModule_Z : realStandardModule 4 (Z d e sd se) =
    realStandardModule 4 [.induced d, .induced e] := by
  have hχ : realPositionCharacter (Z d e sd se) =
      realPositionCharacter [.induced d, .induced e] := by
    funext p x
    rcases p with _ | _ | _ | _ | p <;>
      simp only [realPositionCharacter, realInducedFirstCharacter, realInducedSecondCharacter,
        positiveData_weight, Int.natAbs_natCast, positiveData_exponent]
  ext f
  change f ∈ realStandardModule 4 [.induced (positiveData d sd), .induced (positiveData e se)] ↔ _
  rw [mem_induced_pair_iff, mem_induced_pair_iff, hχ]
  simp only [positiveData_weight, Int.abs_eq_natAbs, Int.natAbs_natCast]

theorem KF_Z : KF 4 (Z d e sd se) = KF 4 [.induced d, .induced e] :=
  congrArg (fun V => kFiniteFunctions V (unitaryCompact ℝ 4)) (standardModule_Z d e sd se)

/-- The actual tail quotient with codomain given by the original induction data. -/
def quotientMap : KF 4 (X d e sd se) →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  (ofEqMap (KF_Z d e sd se)).comp (T d e sd se hd he)

/-- Its explicit linear section. -/
def quotientSection : KF 4 [.induced d, .induced e] →ₗ[ℂ] KF 4 (X d e sd se) :=
  (S d e sd se hd he).comp (ofEqMap (KF_Z d e sd se).symm)

theorem quotient_section (f : KF 4 [.induced d, .induced e]) :
    quotientMap d e sd se hd he (quotientSection d e sd se hd he f) = f :=
  transport_section (KF_Z d e sd se) (T d e sd se hd he) (S d e sd se hd he)
    (T_S d e sd se hd he) f

theorem quotient_surjective : Function.Surjective (quotientMap d e sd se hd he) :=
  fun f => ⟨quotientSection d e sd se hd he f, quotient_section d e sd se hd he f⟩

theorem quotient_exact : IsRealIntertwinerModulo 4 (X d e sd se) [.induced d, .induced e] ⊥
    (quotientMap d e sd se hd he) :=
  modulo_comp_bot (modulo_ofEqMap (KF_Z d e sd se)) (T_exact d e sd se hd he)

theorem ker_quotient : LinearMap.ker (quotientMap d e sd se hd he) =
    LinearMap.range (qd d e sd se) ⊔ LinearMap.range (qe d e sd se) := by
  rw [← ker_T d e sd se hd he]
  ext f
  change ofEqMap (KF_Z d e sd se) (T d e sd se hd he f) = 0 ↔ T d e sd se hd he f = 0
  exact (LinearEquiv.ofEq _ _ (KF_Z d e sd se)).injective.eq_iff' (by rfl)

/-! ## Descent by the two explicit low-mode generators -/

/-- Killing both binomial images is the concrete criterion for descent through the quotient. -/
theorem descend {F : List RealBlock} {M : Submodule ℂ (KF 4 F)}
    (P : KF 4 (X d e sd se) →ₗ[ℂ] KF 4 F)
    (hP : IsRealIntertwinerModulo 4 (X d e sd se) F M P)
    (hqd : P.comp (qd d e sd se) = 0) (hqe : P.comp (qe d e sd se) = 0) :
    let Q := P.comp (quotientSection d e sd se hd he)
    IsRealIntertwinerModulo 4 [.induced d, .induced e] F M Q ∧
      Q.comp (quotientMap d e sd se hd he) = P ∧ LinearMap.range Q = LinearMap.range P := by
  let T' := quotientMap d e sd se hd he
  let S' := quotientSection d e sd se hd he
  have hkill : LinearMap.ker T' ≤ LinearMap.ker P := by
    rw [ker_quotient d e sd se hd he]
    apply sup_le
    · rintro _ ⟨f, rfl⟩
      exact LinearMap.congr_fun hqd f
    · rintro _ ⟨f, rfl⟩
      exact LinearMap.congr_fun hqe f
  have hfac : (P.comp S').comp T' = P := by
    apply LinearMap.ext
    intro f
    have hz : f - S' (T' f) ∈ LinearMap.ker T' := by
      rw [LinearMap.mem_ker, map_sub, quotient_section d e sd se hd he, sub_self]
    have hp := hkill hz
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hp
    exact hp.symm
  refine ⟨modulo_of_comp_surjective hP (quotient_exact d e sd se hd he)
    (quotient_surjective d e sd se hd he) hfac, hfac, ?_⟩
  apply le_antisymm (LinearMap.range_comp_le_range S' P)
  rintro _ ⟨f, rfl⟩
  exact ⟨T' f, LinearMap.congr_fun hfac f⟩

end RealInducedPairQuotientPresentation

open RealInducedPairQuotientPresentation RealStandardFiltration in
/-- Two ascending character pairs present the actual two-induced-block module as a split
linear quotient, with two explicit binomial kernel generators and exact intertwiner descent. -/
def RealInducedPairQuotientPresentationStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (sd se : Fin 2)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs),
    (∀ f, quotientMap d e sd se hd he (quotientSection d e sd se hd he f) = f) ∧
    Function.Surjective (quotientMap d e sd se hd he) ∧
    IsRealIntertwinerModulo 4 (X d e sd se) [.induced d, .induced e] ⊥
      (quotientMap d e sd se hd he) ∧
    LinearMap.ker (quotientMap d e sd se hd he) =
      LinearMap.range (qd d e sd se) ⊔ LinearMap.range (qe d e sd se) ∧
    ∀ (F : List RealBlock) (M : Submodule ℂ (KF 4 F))
      (P : KF 4 (X d e sd se) →ₗ[ℂ] KF 4 F),
      IsRealIntertwinerModulo 4 (X d e sd se) F M P →
      P.comp (qd d e sd se) = 0 → P.comp (qe d e sd se) = 0 →
      let Q := P.comp (quotientSection d e sd se hd he)
      IsRealIntertwinerModulo 4 [.induced d, .induced e] F M Q ∧
        Q.comp (quotientMap d e sd se hd he) = P ∧ LinearMap.range Q = LinearMap.range P

open RealInducedPairQuotientPresentation in
theorem realInducedPairQuotientPresentation : RealInducedPairQuotientPresentationStatement := by
  intro d e sd se hd he
  exact ⟨quotient_section d e sd se hd he, quotient_surjective d e sd se hd he,
    quotient_exact d e sd se hd he, ker_quotient d e sd se hd he,
    fun F M P hP hqd hqe => descend d e sd se hd he P hP hqd hqe⟩

end Langlands.Archimedean
