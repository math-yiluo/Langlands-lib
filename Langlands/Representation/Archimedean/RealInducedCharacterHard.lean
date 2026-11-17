import Langlands.Representation.Archimedean.RealInducedCharacterPushforward
import Langlands.Representation.Archimedean.RealKTypeTransport
import Langlands.Representation.Archimedean.RealOrthogonalUncertainty

/-!
# The induced–character filtration on `GL₃(ℝ)`: the case `t_c - a = -m'`
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealInducedCharacter

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open Langlands.LocalFactor.Archimedean

/-! ## General facts -/

section General

variable {n : ℕ}

/-- A linear map with the same values as an exact intertwiner is an exact intertwiner. -/
theorem modulo_of_coe_eq {ds es es' : List RealBlock} {q : KF n ds →ₗ[ℂ] KF n es}
    {q' : KF n ds →ₗ[ℂ] KF n es'} (hq : IsRealIntertwinerModulo n ds es ⊥ q)
    (h : ∀ f, ((q' f : KF n es') : Langlands.GeneralLinear n ℝ → ℂ) =
      ((q f : KF n es) : Langlands.GeneralLinear n ℝ → ℂ)) :
    IsRealIntertwinerModulo n ds es' ⊥ q' := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hg, hm⟩ := hq.1 k f
    refine ⟨hf, rightTranslation_mem_kFiniteFunctions_realStandardModule n es' (q' f).2 k.2, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at hm ⊢
    apply Subtype.ext
    have e := congrArg Subtype.val hm
    simp only at e
    simp only [h]
    exact e
  · obtain ⟨hf, hg, hm⟩ := hq.2 X f
    refine ⟨hf, rightDerivative_mem_kFiniteFunctions_realStandardModule n es' (q' f).2 X, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at hm ⊢
    apply Subtype.ext
    have e := congrArg Subtype.val hm
    simp only at e
    simp only [h]
    exact e

variable {ds es : List RealBlock} {p : ℕ} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}

/-- If the Frobenius map kills `f`, the block Fourier coefficients of `f` vanish on `O(n)` where
the multiplier does not. -/
theorem coeff_eq_zero_of_blockFrobMap_eq_zero (h : IsBlockFrobData n ds es p ε σ μ)
    {f : KF n ds} (hf : blockFrobMap h f = 0) {j : ℤ} (hj : μ j ≠ 0)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n p j f k = 0 := by
  have e := blockFourierCoefficient_blockFrobMap h f hk j
  rw [hf, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_left hj

/-- A Frobenius map whose multiplier has no zeros on the parity class is injective. -/
theorem eq_zero_of_blockFrobMap_eq_zero (h : IsBlockFrobData n ds es p ε σ μ)
    (hμ : ∀ j : ℤ, Even (j - ε) → μ j ≠ 0) {f : KF n ds} (hf : blockFrobMap h f = 0) :
    f = 0 := by
  refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
  rw [ZeroMemClass.coe_zero, blockFourierCoefficient_zero]
  by_cases hj : Even (j - ε)
  · exact coeff_eq_zero_of_blockFrobMap_eq_zero h hf (hμ j hj) hk
  · exact blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj k

end General

/-! ## The lists -/

section Lists

variable (d : ComplexCharacterData) (c : RealCharacterData)

/-- The sign `|m| + 1 (mod 2)` of the first position of the induction block. -/
abbrev sl : Fin 2 := ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩

/-- The list `[sgn^{|m|+1} |·|^a, c, |·|^b]` between the two standard modules. -/
abbrev midList : List RealBlock :=
  [RealBlock.character (ca d (sl d)), RealBlock.character c, RealBlock.character (cb d 0)]

/-- The principal series of `[sgn^{|m|+1} |·|^a, |·|^b, c]` is that of `[d, c]`. -/
theorem realPositionCharacter_V :
    realPositionCharacter [RealBlock.character (ca d (sl d)), RealBlock.character (cb d 0),
        RealBlock.character c] =
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | i <;> rfl

/-- The principal series of `[c, sgn^{|m|+1} |·|^a, |·|^b]` is that of `[c, d]`. -/
theorem realPositionCharacter_S :
    realPositionCharacter [RealBlock.character c, RealBlock.character (ca d (sl d)),
        RealBlock.character (cb d 0)] =
      realPositionCharacter [RealBlock.character c, RealBlock.induced d] := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | i <;> rfl

theorem hsigma0_ca : sigma0 c (ca d (sl d)) = (-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val) := by
  rw [sigma0_eq]
  simp only [ca_parity]
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := d.weight.natAbs + 1 + _)]
  congr 1
  omega

theorem hsigma0_ca' : sigma0 (ca d (sl d)) c =
    (-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val) := by
  rw [sigma0_eq, mul_comm, ← sigma0_eq]
  exact hsigma0_ca d c

theorem hsigma0_cb : sigma0 (cb d 0) c = (-1 : ℂ) ^ c.parity.val := by
  rw [sigma0_eq, cb_parity, Fin.val_zero, pow_zero, one_mul]

theorem heven_pairParity_ca :
    Even (pairParity c (ca d (sl d)) - ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)) := by
  rw [Int.even_iff]
  simp only [pairParity, ca_parity, sl, Fin.val_mk]
  omega

theorem heven_pairParity_ca' :
    Even (pairParity (ca d (sl d)) c - ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)) := by
  rw [Int.even_iff]
  simp only [pairParity, ca_parity, sl, Fin.val_mk]
  omega

theorem heven_pairParity_cb : Even (pairParity (cb d 0) c - (c.parity.val : ℤ)) := by
  rw [Int.even_iff]
  simp only [pairParity, cb_parity, Fin.val_zero]
  omega

/-- The Frobenius data along the block `0` from `[c, d]` to `midList`. -/
theorem data_S {μ : ℤ → ℂ}
    (hsym : IsSymmetric (pairParity c (ca d (sl d))) (sigma0 c (ca d (sl d))) μ) :
    IsBlockFrobData 3 [RealBlock.character c, RealBlock.induced d] (midList d c) 0
      (pairParity c (ca d (sl d))) (sigma0 c (ca d (sl d))) μ := by
  refine
    { lt := by norm_num
      rank := rfl
      sign_off := fun i hi1 hi2 => ?_
      exp_off := fun i hi1 hi2 => ?_
      exp_p := rfl
      exp_q := rfl
      par := ?_
      sym := hsym
      sign_p := ?_
      sign_q := ?_
      induced_off := ?_
      induced_p := ?_ }
  · rcases i with _ | _ | _ | i
    · exact absurd rfl hi1
    · exact absurd rfl hi2
    · rfl
    · rfl
  · rcases i with _ | _ | _ | i
    · exact absurd rfl hi1
    · exact absurd rfl hi2
    · rfl
    · rfl
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one, neg_one_pow_pairParity']
    rfl
  · rw [realPositionCharacter_neg_one, sigma0_eq]
    show (-1 : ℂ) ^ (sl d).val = (-1) ^ c.parity.val * ((-1) ^ c.parity.val * (-1) ^ (sl d).val)
    linear_combination -(-1 : ℂ) ^ (sl d).val * neg_one_pow_sq_fin c.parity
  · rw [realPositionCharacter_neg_one, sigma0_eq]
    show (-1 : ℂ) ^ c.parity.val = (-1) ^ (sl d).val * ((-1) ^ c.parity.val * (-1) ^ (sl d).val)
    linear_combination -(-1 : ℂ) ^ c.parity.val * neg_one_pow_sq_fin (sl d)
  · intro i e _ he
    rcases i with _ | _ | _ | i <;> simp [realInducedBlockAt] at he
  · intro e he
    simp [realInducedBlockAt] at he

/-- The Frobenius data along the block `1` from `[d, c]` to `midList`. -/
theorem data_V {μ : ℤ → ℂ}
    (hsym : IsSymmetric (pairParity (cb d 0) c) (sigma0 (cb d 0) c) μ) :
    IsBlockFrobData 3 [RealBlock.induced d, RealBlock.character c] (midList d c) 1
      (pairParity (cb d 0) c) (sigma0 (cb d 0) c) μ := by
  refine
    { lt := by norm_num
      rank := rfl
      sign_off := fun i hi1 hi2 => ?_
      exp_off := fun i hi1 hi2 => ?_
      exp_p := rfl
      exp_q := rfl
      par := ?_
      sym := hsym
      sign_p := ?_
      sign_q := ?_
      induced_off := ?_
      induced_p := ?_ }
  · rcases i with _ | _ | _ | i
    · rfl
    · exact absurd rfl hi1
    · exact absurd rfl hi2
    · rfl
  · rcases i with _ | _ | _ | i
    · rfl
    · exact absurd rfl hi1
    · exact absurd rfl hi2
    · rfl
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one, neg_one_pow_pairParity']
    rfl
  · rw [realPositionCharacter_neg_one, sigma0_eq]
    show (-1 : ℂ) ^ c.parity.val = (-1) ^ (0 : Fin 2).val *
      ((-1) ^ (0 : Fin 2).val * (-1) ^ c.parity.val)
    simp
  · rw [realPositionCharacter_neg_one, sigma0_eq]
    show (-1 : ℂ) ^ (0 : Fin 2).val = (-1) ^ c.parity.val *
      ((-1) ^ (0 : Fin 2).val * (-1) ^ c.parity.val)
    simp only [Fin.val_zero, pow_zero, one_mul]
    rw [← sq, neg_one_pow_sq_fin]
  · intro i e _ he
    rcases i with _ | _ | _ | i <;> simp [realInducedBlockAt] at he
  · intro e he
    simp [realInducedBlockAt] at he

end Lists

/-! ## The hard case -/

section Hard

variable {d : ComplexCharacterData} {c : RealCharacterData} {m' : ℕ}

/-- If a Frobenius map with the tail multiplier `tailMultiplier ℓ` kills `f`, the block Fourier
coefficients of weight `|j| ≥ ℓ` of `f` vanish on `O(n)`. -/
theorem highModes_of_tail_frob_eq_zero {n : ℕ} {ds es : List RealBlock} {p ℓ : ℕ} {ε : ℤ}
    {σ : ℂ} (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (hσ : σ ^ 2 = 1) (h : IsBlockFrobData n ds es p ε σ (tailMultiplier ℓ ε σ)) {f : KF n ds}
    (hf : blockFrobMap h f = 0) :
    ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, (ℓ : ℤ) ≤ |j| → blockFourierCoefficient n p j f g = 0 := by
  intro g hg j hj
  by_cases hje : Even (j - ε)
  · refine coeff_eq_zero_of_blockFrobMap_eq_zero h hf ?_ hg
    rw [tailMultiplier_ne_zero_iff hℓ hε hpar hσ hje]
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact hlt
    · exfalso
      rw [Int.even_iff] at hje hpar
      rcases abs_cases j with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  · exact blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hje g

theorem hard_nu_b (hN : c.exponent - aExp d = -(m' : ℂ)) :
    c.exponent - bExp d = (((d.weight.natAbs : ℤ) - m' : ℤ) : ℂ) := by
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  linear_combination hN + aExp_sub_bExp d

/-- **Case (i) of the hard case.** If `t_c - a = -m'` with `0 < m'`, `2m' < |m|` and
`ε_c - m' - |m|` even, there is a bijective exact intertwiner from the standard module of
`[c, d]` to that of `[d, c]`: the composite of the tail map along the block `0` into
`[sgn^{|m|+1} |·|^a, c, |·|^b]` and the generic swap of the last two characters. -/
theorem hard_iso_even (hL' : RealSwapLandingCharacterFirstStatement) (hm' : 0 < m')
    (hml : 2 * m' < d.weight.natAbs) (hN : c.exponent - aExp d = -(m' : ℂ))
    (hpar : Even ((c.parity.val : ℤ) - m' - d.weight.natAbs)) :
    ∃ L : KF 3 [RealBlock.character c, RealBlock.induced d] →ₗ[ℂ]
        KF 3 [RealBlock.induced d, RealBlock.character c],
      IsRealIntertwinerModulo 3 [RealBlock.character c, RealBlock.induced d]
        [RealBlock.induced d, RealBlock.character c] ⊥ L ∧ Function.Surjective L := by
  have hε₀ := pairParity_eq c (ca d (sl d))
  have hε₁ := pairParity_eq (cb d 0) c
  have hpar₀ : Even ((m' : ℤ) - 1 - pairParity c (ca d (sl d))) := by
    rw [Int.even_iff] at hpar ⊢
    simp only [pairParity, ca_parity, sl, Fin.val_mk]
    omega
  have hνre : 0 < (c.exponent - bExp d).re := by
    rw [hard_nu_b hN, Complex.intCast_re]
    have : (0 : ℤ) < (d.weight.natAbs : ℤ) - m' := by omega
    exact_mod_cast this
  have hne₁ : ∀ k : ℕ, c.exponent - bExp d ≠ (pairParity (cb d 0) c : ℂ) + 2 * k + 1 := by
    intro k hk
    rw [hard_nu_b hN] at hk
    have hk' : ((d.weight.natAbs : ℤ) - m') = pairParity (cb d 0) c + 2 * k + 1 := by
      exact_mod_cast hk
    rw [Int.even_iff] at hpar
    simp only [pairParity, cb_parity, Fin.val_zero] at hk'
    omega
  have hσ₀ : sigma0 c (ca d (sl d)) ^ 2 = 1 := neg_one_pow_sq _
  have hsym₀ : IsSymmetric (pairParity c (ca d (sl d))) (sigma0 c (ca d (sl d)))
      (tailMultiplier m' (pairParity c (ca d (sl d))) (sigma0 c (ca d (sl d)))) :=
    isSymmetric_tailMultiplier hm' hε₀ hpar₀ hσ₀
  have hrec₀ : IsRecurrent (1 - (m' : ℂ)) (pairParity c (ca d (sl d)))
      (tailMultiplier m' (pairParity c (ca d (sl d))) (sigma0 c (ca d (sl d)))) :=
    isRecurrent_tailMultiplier hm' hε₀ hpar₀ hσ₀
  have hsym₁ : IsSymmetric (pairParity (cb d 0) c) (sigma0 (cb d 0) c)
      (genericMultiplier (c.exponent - bExp d) (pairParity (cb d 0) c)) :=
    isSymmetric_genericMultiplier _ hε₁
  have hrec₁ : IsRecurrent (c.exponent - bExp d + 1) (pairParity (cb d 0) c)
      (genericMultiplier (c.exponent - bExp d) (pairParity (cb d 0) c)) :=
    isRecurrent_genericMultiplier hνre hε₁
  have hμ₁ := genericMultiplier_ne_zero hνre hε₁ hne₁
  let A₀ := data_S d c hsym₀
  let A₁ := data_swap (pre := [RealBlock.character (ca d (sl d))]) (post := []) (n := 3)
    (c := cb d 0) (d := c) rfl hsym₁
  have hA₀ : IsRealIntertwinerModulo 3 _ _ ⊥ (blockFrobMap A₀) :=
    isRealIntertwinerModulo_blockFrobMap A₀ (by
      show IsRecurrent (c.exponent - aExp d + 1) _ _
      rw [hN, neg_add_eq_sub]
      exact hrec₀) ⊥
  have hA₁ : IsRealIntertwinerModulo 3 _ _ ⊥ (blockFrobMap A₁) :=
    isRealIntertwinerModulo_blockFrobMap A₁
      (by rw [exponent_swp_zero, exponent_swp_one]; exact hrec₁) ⊥
  let F := blockFrobMap A₁ ∘ₗ blockFrobMap A₀
  have hF : IsRealIntertwinerModulo 3 [RealBlock.character c, RealBlock.induced d]
      [RealBlock.character (ca d (sl d)), RealBlock.character (cb d 0), RealBlock.character c]
      ⊥ F :=
    modulo_comp_bot hA₁ hA₀
  have hδ : (1 - (m' : ℂ)) + (d.weight.natAbs : ℂ) = c.exponent - bExp d + 1 := by
    linear_combination -hN - aExp_sub_bExp d
  have hland : ∀ f : KF 3 [RealBlock.character c, RealBlock.induced d],
      (KF 3 [RealBlock.character (ca d (sl d)), RealBlock.character (cb d 0),
        RealBlock.character c]).subtype (F f) ∈
        KF 3 [RealBlock.induced d, RealBlock.character c] := by
    intro f
    refine ⟨RealSwapLandingIntegral.mem_realStandardModule_induced_character d c ?_ ?_, (F f).2.2⟩
    · rw [← realPositionCharacter_V d c]
      exact (F f).2.1.1
    · intro k hk g hg
      refine hL' c d (1 - m') _ _ f (blockFrobMap A₀ f) (F f)
        (RealSwapLandingMirror.isRecurrent_congr hrec₀ (heven_pairParity_ca d c))
        (RealSwapLandingMirror.isSymmetric_congr hsym₀ (heven_pairParity_ca d c) (hsigma0_ca d c))
        (by rw [hδ]; exact RealSwapLandingMirror.isRecurrent_congr hrec₁ (heven_pairParity_cb d c))
        (RealSwapLandingMirror.isSymmetric_congr hsym₁ (heven_pairParity_cb d c) (hsigma0_cb d c))
        f.2 (continuous_coe _) (continuous_coe _)
        (fun g hg k => blockFourierCoefficient_blockFrobMap A₀ f hg k)
        (fun g hg k => blockFourierCoefficient_blockFrobMap A₁ (blockFrobMap A₀ f) hg k)
        g hg k hk
  let M : KF 3 [RealBlock.character c, RealBlock.induced d] →ₗ[ℂ]
      KF 3 [RealBlock.induced d, RealBlock.character c] :=
    LinearMap.codRestrict _ ((KF 3 [RealBlock.character (ca d (sl d)),
      RealBlock.character (cb d 0), RealBlock.character c]).subtype ∘ₗ F) hland
  have hM : IsRealIntertwinerModulo 3 [RealBlock.character c, RealBlock.induced d]
      [RealBlock.induced d, RealBlock.character c] ⊥ M :=
    modulo_of_coe_eq hF fun _ => rfl
  have hinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).mpr fun f hf => ?_
    have hF0 : F f = 0 := Subtype.ext (by
      have e := congrArg Subtype.val hf
      exact e)
    have h0 : blockFrobMap A₀ f = 0 :=
      eq_zero_of_blockFrobMap_eq_zero A₁ (fun j _ => hμ₁ j) hF0
    have hhigh := highModes_of_tail_frob_eq_zero hm' hε₀ hpar₀ hσ₀ A₀ h0
    have hlow : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, |j| < (d.weight.natAbs : ℤ) →
        blockFourierCoefficient 3 1 j f g = 0 := fun g _ j hj =>
      f.2.1.2 1 d rfl j (by rw [Int.abs_eq_natAbs d.weight]; exact hj) g
    have hK := RealOrthogonalUncertainty.realOrthogonalBlockUncertainty 1 0
      d.weight.natAbs m' f (Or.inr ⟨rfl, rfl⟩) (by omega) (continuous_coe f) f.2.2 hlow hhigh
    exact Subtype.ext (eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1.1 hK)
  exact ⟨M, hM, RealKTypeTransport.surjective_of_injective_character_induced c d
    hM.isRealKEquivariant hinj⟩

/-- **Case (ii) of the hard case.** If `t_c - a = -m'` with `0 < m'`, `2m' < |m|` and
`ε_c - m' - |m|` odd, there is a bijective exact intertwiner from the standard module of
`[d, c]` to that of `[c, d]`: the composite of the tail map along the block `1` into
`[sgn^{|m|+1} |·|^a, c, |·|^b]` and the generic swap of the first two characters. Its inverse
is a bijective exact intertwiner from `[c, d]` to `[d, c]`. -/
theorem hard_iso_odd (hL : RealSwapLandingInducedFirstStatement) (hm' : 0 < m')
    (hml : 2 * m' < d.weight.natAbs) (hN : c.exponent - aExp d = -(m' : ℂ))
    (hpar : ¬ Even ((c.parity.val : ℤ) - m' - d.weight.natAbs)) :
    ∃ L : KF 3 [RealBlock.character c, RealBlock.induced d] →ₗ[ℂ]
        KF 3 [RealBlock.induced d, RealBlock.character c],
      IsRealIntertwinerModulo 3 [RealBlock.character c, RealBlock.induced d]
        [RealBlock.induced d, RealBlock.character c] ⊥ L ∧ Function.Surjective L := by
  have hε₀ := pairParity_eq c (ca d (sl d))
  have hε₁ := pairParity_eq (cb d 0) c
  have hl' : 0 < d.weight.natAbs - m' := by omega
  have hpar₁ : Even (((d.weight.natAbs - m' : ℕ) : ℤ) - 1 - pairParity (cb d 0) c) := by
    rw [Int.even_iff] at hpar ⊢
    simp only [pairParity, cb_parity, Fin.val_zero]
    omega
  have hν : aExp d - c.exponent = (m' : ℂ) := by linear_combination -hN
  have hνre : 0 < (aExp d - c.exponent).re := by
    rw [hν, Complex.natCast_re]
    exact_mod_cast hm'
  have hne₀ : ∀ k : ℕ, aExp d - c.exponent ≠ (pairParity c (ca d (sl d)) : ℂ) + 2 * k + 1 := by
    intro k hk
    rw [hν] at hk
    have hk' : (m' : ℤ) = pairParity c (ca d (sl d)) + 2 * k + 1 := by exact_mod_cast hk
    rw [Int.even_iff] at hpar
    simp only [pairParity, ca_parity, sl, Fin.val_mk] at hk'
    omega
  have hσ₁ : sigma0 (cb d 0) c ^ 2 = 1 := neg_one_pow_sq _
  have hsym₁ : IsSymmetric (pairParity (cb d 0) c) (sigma0 (cb d 0) c)
      (tailMultiplier (d.weight.natAbs - m') (pairParity (cb d 0) c) (sigma0 (cb d 0) c)) :=
    isSymmetric_tailMultiplier hl' hε₁ hpar₁ hσ₁
  have hrec₁ : IsRecurrent (1 - ((d.weight.natAbs - m' : ℕ) : ℂ)) (pairParity (cb d 0) c)
      (tailMultiplier (d.weight.natAbs - m') (pairParity (cb d 0) c) (sigma0 (cb d 0) c)) :=
    isRecurrent_tailMultiplier hl' hε₁ hpar₁ hσ₁
  have hsym₀ : IsSymmetric (pairParity c (ca d (sl d))) (sigma0 c (ca d (sl d)))
      (genericMultiplier (aExp d - c.exponent) (pairParity c (ca d (sl d)))) :=
    isSymmetric_genericMultiplier _ hε₀
  have hrec₀ : IsRecurrent (aExp d - c.exponent + 1) (pairParity c (ca d (sl d)))
      (genericMultiplier (aExp d - c.exponent) (pairParity c (ca d (sl d)))) :=
    isRecurrent_genericMultiplier hνre hε₀
  have hμ₀ := genericMultiplier_ne_zero hνre hε₀ hne₀
  have hδ₁ : bExp d - c.exponent + 1 = 1 - ((d.weight.natAbs - m' : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega)]
    linear_combination -hN - aExp_sub_bExp d
  have hδ₀ : (1 - ((d.weight.natAbs - m' : ℕ) : ℂ)) + (d.weight.natAbs : ℂ) =
      aExp d - c.exponent + 1 := by
    rw [Nat.cast_sub (by omega)]
    linear_combination hN
  let B₁ := data_V d c hsym₁
  let B₀ := data_swap (pre := []) (post := [RealBlock.character (cb d 0)]) (n := 3)
    (c := c) (d := ca d (sl d)) rfl hsym₀
  have hB₁ : IsRealIntertwinerModulo 3 _ _ ⊥ (blockFrobMap B₁) :=
    isRealIntertwinerModulo_blockFrobMap B₁ (by
      show IsRecurrent (bExp d - c.exponent + 1) _ _
      rw [hδ₁]
      exact hrec₁) ⊥
  have hB₀ : IsRealIntertwinerModulo 3 _ _ ⊥ (blockFrobMap B₀) :=
    isRealIntertwinerModulo_blockFrobMap B₀
      (by rw [exponent_swp_zero, exponent_swp_one]; exact hrec₀) ⊥
  let F := blockFrobMap B₀ ∘ₗ blockFrobMap B₁
  have hF : IsRealIntertwinerModulo 3 [RealBlock.induced d, RealBlock.character c]
      [RealBlock.character c, RealBlock.character (ca d (sl d)), RealBlock.character (cb d 0)]
      ⊥ F :=
    modulo_comp_bot hB₀ hB₁
  have hland : ∀ f : KF 3 [RealBlock.induced d, RealBlock.character c],
      (KF 3 [RealBlock.character c, RealBlock.character (ca d (sl d)),
        RealBlock.character (cb d 0)]).subtype (F f) ∈
        KF 3 [RealBlock.character c, RealBlock.induced d] := by
    intro f
    refine ⟨RealSwapFLanding.mem_realStandardModule_character_induced c d ?_ ?_, (F f).2.2⟩
    · rw [← realPositionCharacter_S d c]
      exact (F f).2.1.1
    · intro k hk g hg
      refine hL c d (1 - ((d.weight.natAbs - m' : ℕ) : ℂ)) _ _ f (blockFrobMap B₁ f) (F f)
        (RealSwapLandingMirror.isRecurrent_congr hrec₁ (heven_pairParity_cb d c))
        (RealSwapLandingMirror.isSymmetric_congr hsym₁ (heven_pairParity_cb d c) (hsigma0_cb d c))
        (by rw [hδ₀]; exact RealSwapLandingMirror.isRecurrent_congr hrec₀ (heven_pairParity_ca d c))
        (RealSwapLandingMirror.isSymmetric_congr hsym₀ (heven_pairParity_ca d c) (hsigma0_ca d c))
        f.2 (continuous_coe _) (continuous_coe _)
        (fun g hg k => blockFourierCoefficient_blockFrobMap B₁ f hg k)
        (fun g hg k => blockFourierCoefficient_blockFrobMap B₀ (blockFrobMap B₁ f) hg k)
        g hg k hk
  let M : KF 3 [RealBlock.induced d, RealBlock.character c] →ₗ[ℂ]
      KF 3 [RealBlock.character c, RealBlock.induced d] :=
    LinearMap.codRestrict _ ((KF 3 [RealBlock.character c, RealBlock.character (ca d (sl d)),
      RealBlock.character (cb d 0)]).subtype ∘ₗ F) hland
  have hM : IsRealIntertwinerModulo 3 [RealBlock.induced d, RealBlock.character c]
      [RealBlock.character c, RealBlock.induced d] ⊥ M :=
    modulo_of_coe_eq hF fun _ => rfl
  have hinj : Function.Injective M := by
    refine (injective_iff_map_eq_zero M).mpr fun f hf => ?_
    have hF0 : F f = 0 := Subtype.ext (by
      have e := congrArg Subtype.val hf
      exact e)
    have h0 : blockFrobMap B₁ f = 0 :=
      eq_zero_of_blockFrobMap_eq_zero B₀ (fun j _ => hμ₀ j) hF0
    have hhigh := highModes_of_tail_frob_eq_zero hl' hε₁ hpar₁ hσ₁ B₁ h0
    have hlow : ∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, |j| < (d.weight.natAbs : ℤ) →
        blockFourierCoefficient 3 0 j f g = 0 := fun g _ j hj =>
      f.2.1.2 0 d rfl j (by rw [Int.abs_eq_natAbs d.weight]; exact hj) g
    have hK := RealOrthogonalUncertainty.realOrthogonalBlockUncertainty 0 1
      d.weight.natAbs (d.weight.natAbs - m') f (Or.inl ⟨rfl, rfl⟩) (by omega)
      (continuous_coe f) f.2.2 hlow hhigh
    exact Subtype.ext (eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1.1 hK)
  have hsurj : Function.Surjective M :=
    RealKTypeTransport.surjective_of_injective_induced_character c d hM.isRealKEquivariant hinj
  let e := LinearEquiv.ofBijective M ⟨hinj, hsurj⟩
  refine ⟨e.symm.toLinearMap, ?_, e.symm.surjective⟩
  refine modulo_of_comp_surjective (modulo_id _) hM hsurj (LinearMap.ext fun f => ?_)
  exact LinearEquiv.ofBijective_symm_apply_apply (h := ⟨hinj, hsurj⟩) M f

/-- **The hard case.** If `t_c - a = -m'` with `0 < m'` and `2m' < |m|`, the standard module of
`[d, c]` has the one-step filtration with piece `[c, d]`. -/
theorem hard_filtration (hL : RealSwapLandingInducedFirstStatement)
    (hL' : RealSwapLandingCharacterFirstStatement) (hm' : 0 < m')
    (hml : 2 * m' < d.weight.natAbs) (hN : c.exponent - aExp d = -(m' : ℂ)) :
    RealAdjacentFiltration 3 [] [] (RealBlock.induced d) (RealBlock.character c) := by
  obtain ⟨L, hLm, hLs⟩ : ∃ L : KF 3 [RealBlock.character c, RealBlock.induced d] →ₗ[ℂ]
        KF 3 [RealBlock.induced d, RealBlock.character c],
      IsRealIntertwinerModulo 3 [RealBlock.character c, RealBlock.induced d]
        [RealBlock.induced d, RealBlock.character c] ⊥ L ∧ Function.Surjective L := by
    by_cases hpar : Even ((c.parity.val : ℤ) - m' - d.weight.natAbs)
    · exact hard_iso_even hL' hm' hml hN hpar
    · exact hard_iso_odd hL hm' hml hN hpar
  refine ⟨1, fun _ => [RealBlock.character c, RealBlock.induced d], fun _ => L,
    fun _ => Or.inl rfl, fun _ => modulo_mono hLm bot_le, ?_⟩
  exact eq_top_iff.2 fun f _ => Submodule.mem_iSup_of_mem (0 : Fin 1) (hLs f)

end Hard

end RealInducedCharacter

end Langlands.Archimedean
