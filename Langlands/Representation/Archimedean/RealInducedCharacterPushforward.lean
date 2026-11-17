import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealInducedCharacterLanding

/-!
# The induced–character filtration on `GL₃(ℝ)`: the pushforward along the tail maps
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealInducedCharacter

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealSwapFLanding RealJacquetFrobenius
open PrincipalSeriesExtension GramFormula
open Langlands.LocalFactor.Archimedean

/-! ## Signs -/

section Signs

theorem pow_eq_pow_mul_pow_of_mod {x : ℂ} (hx : x ^ 2 = 1) {p q e : ℕ}
    (h : p % 2 = (q + e) % 2) : x ^ p = x ^ q * x ^ e := by
  have key : ∀ k : ℕ, x ^ k = x ^ (k % 2) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k 2, pow_add, pow_mul, hx, one_pow, mul_one]
  rw [← pow_add, key p, key (q + e), h]

/-- The position characters at a sign. -/
theorem realPositionCharacter_signUnit (ds : List RealBlock) (i : ℕ) (x : ℝˣ) :
    realPositionCharacter ds i (signUnit x) =
      ((signReal (x : ℝ) : ℝ) : ℂ) ^ (realPositionSign ds i).val := by
  rw [realPositionCharacter_eq_charFun]
  unfold signUnit signReal
  split_ifs
  · simp [charFun_one]
  · simp [charFun_neg_one]

theorem sgnDet_signDiagonal (a : Fin 3 → ℝˣ) :
    sgnDet 3 (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)))) =
      ∏ i : Fin 3, ((signReal (a i : ℝ) : ℝ) : ℂ) := by
  unfold sgnDet
  have hdet : ((Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) :
      Langlands.GeneralLinear 3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ).det =
        ∏ i : Fin 3, signReal (a i : ℝ) := by
    show (Matrix.diagonal fun i => signReal (a i : ℝ)).det = _
    rw [Matrix.det_diagonal]
  rw [hdet, Finset.abs_prod]
  simp only [abs_signReal, Finset.prod_const_one, div_one, Complex.ofReal_prod]

/-- **Signs of a principal series function.** -/
theorem principalSeries_signDiagonal {ds : List RealBlock} {G : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hG : G ∈ principalSeries ℝ 3 (realPositionCharacter ds)) (a : Fin 3 → ℝˣ)
    (κ : Matrix.unitaryGroup (Fin 3) ℝ) :
    G (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ)) =
      (∏ i : Fin 3, ((signReal (a i : ℝ) : ℝ) : ℂ) ^ (realPositionSign ds i).val) *
        G (Unitary.toUnits κ) := by
  rw [PartialJacquet.signDiagonal_toUnits, hG.2, JacquetKernel.principalSeriesCharacter_sign]
  congr 1
  exact Finset.prod_congr rfl fun i _ => realPositionCharacter_signUnit ds i (a i)

/-- **The sign twist.** If the position signs of `X` agree modulo `2` with those of `Y`
shifted by `e`, a principal series function for `X` transforms under the sign matrices by the
character of `Y` times `sgnDet^e`. -/
theorem principalSeries_signDiagonal_twist {X Y : List RealBlock} (e : ℕ)
    (hXY : ∀ i : Fin 3, (realPositionSign X i).val % 2 = ((realPositionSign Y i).val + e) % 2)
    {G : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hG : G ∈ principalSeries ℝ 3 (realPositionCharacter X)) (a : Fin 3 → ℝˣ)
    (κ : Matrix.unitaryGroup (Fin 3) ℝ) :
    G (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ)) =
      principalSeriesCharacter ℝ 3 (realPositionCharacter Y) (fun i => signUnit (a i)) *
        sgnDet 3 (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)))) ^ e *
          G (Unitary.toUnits κ) := by
  rw [principalSeries_signDiagonal hG, JacquetKernel.principalSeriesCharacter_sign,
    sgnDet_signDiagonal, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [realPositionCharacter_signUnit]
  have hsq : ((signReal (a i : ℝ) : ℝ) : ℂ) ^ 2 = 1 := by
    have h2 : (signReal (a i : ℝ)) ^ 2 = 1 := by rw [← sq_abs, abs_signReal, one_pow]
    rw [← Complex.ofReal_pow, h2, Complex.ofReal_one]
  exact pow_eq_pow_mul_pow_of_mod hsq (hXY i)

end Signs

/-! ## The descent through the tail map -/

section Descent

open RealStandardFiltration

variable {d : ComplexCharacterData} {c : RealCharacterData} {sa sb : Fin 2}

/-- The test character `sgn^{s_a + ε} |·|^s` of the mirror landing. -/
abbrev cTest (c : RealCharacterData) (sa : Fin 2) : RealCharacterData :=
  RealJacquetFrobenius.charData (sa + c.parity) c.exponent

theorem pairParity_ca : pairParity (ca d sa) c = ((cTest c sa).parity.val : ℤ) := by
  simp [pairParity, cTest, RealJacquetFrobenius.charData, Fin.val_add]

theorem sigma0_ca : sigma0 (ca d sa) c = (-1 : ℂ) ^ (cTest c sa).parity.val := by
  rw [sigma0, pairParity_ca, Int.natAbs_natCast]

theorem even_pairParity_cb (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    Even (pairParity (cb d sb) c -
      ((d.weight.natAbs + 1 + (cTest c sa).parity.val : ℕ) : ℤ)) := by
  rw [Int.even_iff]
  simp only [pairParity, cb_parity, cTest, RealJacquetFrobenius.charData, Fin.val_add]
  omega

theorem sigma0_cb (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    sigma0 (cb d sb) c = (-1 : ℂ) ^ (d.weight.natAbs + 1 + (cTest c sa).parity.val) := by
  rw [sigma0, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (n := d.weight.natAbs + 1 + (cTest c sa).parity.val)]
  congr 1
  simp only [pairParity, cb_parity, cTest, RealJacquetFrobenius.charData, Fin.val_add,
    Int.natAbs_natCast]
  omega

/-- The block-`1` Fourier coefficients of weight `|j| ≥ ℓ` of a function killed by the tail
map at position `1` vanish. -/
theorem highModes_of_tail_eq_zero (hl : 0 < d.weight.natAbs)
    (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    (g : KF 3 ([RealBlock.character c] ++
      [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ []))
    (hg : blockFrobMap (data_tail (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs)
      g = 0) :
    ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j g x = 0 := by
  intro j hj x hx
  have h := data_tail (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs
  have hε := pairParity_eq (cb d sb) (ca d sa)
  have hpar := tail_parity (d := d) hs
  by_cases hje : Even (j - pairParity (cb d sb) (ca d sa))
  · have hlt : (d.weight.natAbs : ℤ) < |j| := by
      rw [Int.abs_eq_natAbs] at hj
      rcases hj.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        obtain ⟨r, hr⟩ := hpar
        obtain ⟨t, ht⟩ := hje
        rcases abs_cases j with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] at heq <;> omega
    have hne := (tailMultiplier_ne_zero_iff hl hε hpar (neg_one_pow_sq_fin sa) hje).mpr hlt
    have h1 := blockFourierCoefficient_blockFrobMap h g hx j
    rw [hg] at h1
    have h0 : blockFourierCoefficient 3 (realRank [RealBlock.character c]) j
        (((0 : KF 3 ([RealBlock.character c] ++ [RealBlock.induced d] ++ [])) :
          Langlands.GeneralLinear 3 ℝ → ℂ)) x = 0 := blockFourierCoefficient_zero j x
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hne
  · exact blockFourierCoefficient_eq_zero_of_not_even h.lt h.par g hje x

/-- The position signs of `[sgn^{s_b}|·|^a, sgn^{s_a}|·|^b, c]` are those of `[d, c']`
shifted by `s_a`. -/
theorem sign_high_twist (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) :
    ∀ i : Fin 3, (realPositionSign ([] ++ [RealBlock.character (RealJacquetFrobenius.charData sb
        (aExp d)), RealBlock.character (RealJacquetFrobenius.charData sa (bExp d))] ++
          [RealBlock.character c]) i).val % 2 =
      ((realPositionSign [RealBlock.induced d, RealBlock.character (cTest c sa)] i).val +
        sa.val) % 2 := by
  intro i
  fin_cases i <;>
    simp [realPositionSign, RealJacquetFrobenius.charData, cTest, Fin.val_add] <;> omega

/-- **Descent.** A function `g` of the standard module of `[c, c_b, c_a]` killed by the tail
map at position `1` is killed by `T₀ ∘ Q₁ ∘ Q₂`, where `Q₂` swaps `c` and `c_b`, `Q₁` swaps `c`
and `c_a`, and `T₀` is the tail map at position `0` onto `[d, c]`. -/
theorem descent (hL : RealSwapLandingInducedFirstStatement)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    {μ₀ μ₁ : ℤ → ℂ}
    (hsym₀ : IsSymmetric (pairParity (cb d sb) c) (sigma0 (cb d sb) c) μ₀)
    (hsym₁ : IsSymmetric (pairParity (ca d sa) c) (sigma0 (ca d sa) c) μ₁)
    (hrec₀ : IsRecurrent (c.exponent - bExp d + 1) (pairParity (cb d sb) c) μ₀)
    (hrec₁ : IsRecurrent (c.exponent - aExp d + 1) (pairParity (ca d sa) c) μ₁)
    (g : KF 3 ([RealBlock.character c] ++
      [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ []))
    (hg : blockFrobMap (data_tail (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs)
      g = 0) :
    blockFrobMap (data_tail (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs)
      (blockFrobMap (data_swap (pre := [RealBlock.character (cb d sb)]) (post := []) (n := 3)
          rfl hsym₁)
        (blockFrobMap (data_swap (pre := []) (post := [RealBlock.character (ca d sa)]) (n := 3)
          rfl hsym₀) g)) = 0 := by
  set Q₂ := data_swap (pre := []) (post := [RealBlock.character (ca d sa)]) (n := 3) rfl hsym₀
  set Q₁ := data_swap (pre := [RealBlock.character (cb d sb)]) (post := []) (n := 3) rfl hsym₁
  set g₁ := blockFrobMap Q₂ g with hg₁
  set g₂ := blockFrobMap Q₁ g₁ with hg₂
  have H := data_high (pre := []) (post := [RealBlock.character c]) (n := 3) (d := d)
    (sa := sa) (sb := sb) rfl
  set G := blockFrobMap H g₂ with hG
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  refine tail_eq_zero (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs g₂ ?_
  have hδ : c.exponent - bExp d + 1 = (c.exponent - aExp d + 1) + (d.weight.natAbs : ℂ) := by
    have := aExp_sub_bExp d
    linear_combination this
  have hμ₁r : IsRecurrent (c.exponent - aExp d + 1) ((cTest c sa).parity.val : ℤ) μ₁ :=
    RealSwapLandingMirror.isRecurrent_congr hrec₁ (by simp [pairParity_ca])
  have hμ₁s : IsSymmetric ((cTest c sa).parity.val : ℤ) ((-1 : ℂ) ^ (cTest c sa).parity.val) μ₁ :=
    RealSwapLandingMirror.isSymmetric_congr hsym₁ (by simp [pairParity_ca]) sigma0_ca
  have hμ₀r : IsRecurrent ((c.exponent - aExp d + 1) + (d.weight.natAbs : ℂ))
      ((d.weight.natAbs + 1 + (cTest c sa).parity.val : ℕ) : ℤ) μ₀ := by
    rw [← hδ]
    exact RealSwapLandingMirror.isRecurrent_congr hrec₀ (even_pairParity_cb hs)
  have hμ₀s := RealSwapLandingMirror.isSymmetric_congr hsym₀ (even_pairParity_cb hs) (sigma0_cb hs)
  refine highModes_eq_zero_mirror hL (cTest c sa) d (c.exponent - aExp d + 1) μ₀ μ₁
    hμ₁r hμ₁s hμ₀r hμ₀s sa.val (continuous_coe g) (continuous_coe g₁) (continuous_coe g₂)
    (continuous_coe G) g.2.2 g₁.2.2 g₂.2.2 G.2.2 (highModes_of_tail_eq_zero hl hs g hg)
    (fun j x hx => blockFourierCoefficient_blockFrobMap Q₂ g hx j)
    (fun j x hx => blockFourierCoefficient_blockFrobMap Q₁ g₁ hx j) ?_ ?_
    (principalSeries_signDiagonal_twist sa.val (sign_high_twist hs) G.2.1.1)
  · intro j hj x hx
    refine (blockFourierCoefficient_blockFrobMap H g₂ hx j).trans ?_
    have h' : (d.weight.natAbs : ℤ) ≤ |j| := by rwa [habs] at hj
    simp only [highIndicator, h', ↓reduceIte, one_mul]
    rfl
  · intro j hj x hx
    refine (blockFourierCoefficient_blockFrobMap H g₂ hx j).trans ?_
    have h' : ¬ (d.weight.natAbs : ℤ) ≤ |j| := by rw [habs] at hj; exact not_le.mpr hj
    simp only [highIndicator, h', ↓reduceIte, zero_mul]

/-- **The lift.** Under the hypotheses of `descent` (with the recurrences of the two swaps),
there is an exact intertwiner `L` from the standard module of `[c, d]` to that of `[d, c]`
with `L ∘ T₁ = T₀ ∘ Q₁ ∘ Q₂`. -/
theorem exists_lift (hL : RealSwapLandingInducedFirstStatement)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    {μ₀ μ₁ : ℤ → ℂ}
    (hsym₀ : IsSymmetric (pairParity (cb d sb) c) (sigma0 (cb d sb) c) μ₀)
    (hsym₁ : IsSymmetric (pairParity (ca d sa) c) (sigma0 (ca d sa) c) μ₁)
    (hrec₀ : IsRecurrent (c.exponent - bExp d + 1) (pairParity (cb d sb) c) μ₀)
    (hrec₁ : IsRecurrent (c.exponent - aExp d + 1) (pairParity (ca d sa) c) μ₁) :
    ∃ L : KF 3 [RealBlock.character c, RealBlock.induced d] →ₗ[ℂ]
        KF 3 [RealBlock.induced d, RealBlock.character c],
      IsRealIntertwinerModulo 3 [RealBlock.character c, RealBlock.induced d]
        [RealBlock.induced d, RealBlock.character c] ⊥ L ∧
      ∀ g, L (blockFrobMap (data_tail (pre := [RealBlock.character c]) (post := []) (n := 3)
          rfl hl hs) g) =
        blockFrobMap (data_tail (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs)
          (blockFrobMap (data_swap (pre := [RealBlock.character (cb d sb)]) (post := [])
              (n := 3) rfl hsym₁)
            (blockFrobMap (data_swap (pre := []) (post := [RealBlock.character (ca d sa)])
              (n := 3) rfl hsym₀) g)) := by
  set T₀ := data_tail (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs
  set T₁ := data_tail (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs
  set T₁' := data_tailInv (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs
  set Q₂ := data_swap (pre := []) (post := [RealBlock.character (ca d sa)]) (n := 3) rfl hsym₀
  set Q₁ := data_swap (pre := [RealBlock.character (cb d sb)]) (post := []) (n := 3) rfl hsym₁
  have hQ₂ : IsRealIntertwinerModulo 3 _ _ ⊥ (blockFrobMap Q₂) :=
    isRealIntertwinerModulo_blockFrobMap Q₂
      (by rw [exponent_swp_zero, exponent_swp_one]; exact hrec₀) ⊥
  have hQ₁ : IsRealIntertwinerModulo 3 _ _ ⊥ (blockFrobMap Q₁) :=
    isRealIntertwinerModulo_blockFrobMap Q₁
      (by rw [exponent_swp_zero, exponent_swp_one]; exact hrec₁) ⊥
  let F := blockFrobMap T₀ ∘ₗ blockFrobMap Q₁ ∘ₗ blockFrobMap Q₂
  have hF : IsRealIntertwinerModulo 3 _ _ ⊥ F :=
    modulo_comp_bot (modulo_tail (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs)
      (modulo_comp_bot hQ₁ hQ₂)
  have hfac : ∀ g, (F ∘ₗ blockFrobMap T₁') (blockFrobMap T₁ g) = F g := by
    intro g
    have h0 : blockFrobMap T₁ (blockFrobMap T₁' (blockFrobMap T₁ g) - g) = 0 := by
      rw [map_sub, tail_tailInv (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs,
        sub_self]
    have h := descent hL hl hs hsym₀ hsym₁ hrec₀ hrec₁ _ h0
    rw [map_sub, map_sub, map_sub, sub_eq_zero] at h
    exact h
  refine ⟨F ∘ₗ blockFrobMap T₁', ?_, hfac⟩
  exact modulo_of_comp_surjective hF
    (modulo_tail (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs)
    (tail_surjective (pre := [RealBlock.character c]) (post := []) (n := 3) rfl hl hs)
    (LinearMap.ext hfac)

end Descent

/-! ## The swaps and the reducible pieces -/

section Swap

variable {n : ℕ} {pre post : List RealBlock} {c d : RealCharacterData} {ℓ : ℕ}

/-- A swap with a multiplier without zeros is surjective. -/
theorem swap_surjective {μ : ℤ → ℂ}
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hsym : IsSymmetric (pairParity c d) (sigma0 c d) μ) (hμ : ∀ k, μ k ≠ 0) :
    Function.Surjective (blockFrobMap (data_swap hn hsym)) := fun f =>
  ⟨blockFrobMap (data_unswap hn hsym) f,
    blockFrobMap_blockFrobMap_eq (data_unswap hn hsym) (data_swap hn hsym) f
      fun j _ hne => absurd (mul_inv_cancel₀ (hμ j)) hne⟩

/-- **The reducible pieces** (after the proof of `realAdjacentFiltration_of_reducible`). If
`t_d - t_c = ℓ` is a positive integer with `ℓ - 1 ≡ pairParity c d (mod 2)`, the map `q₁` out
of the induction block is an intertwiner modulo the range of the binomial swap `q₀`, and the
two ranges span. -/
theorem reducible_pieces
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (hν : d.exponent - c.exponent = ℓ) :
    IsRealIntertwinerModulo n (pre ++ indBlock c d ℓ ++ post)
        (pre ++ RealBlock.character c :: RealBlock.character d :: post)
        (LinearMap.range (blockFrobMap (data_q0 (ℓ := ℓ) hn)))
        (blockFrobMap (data_q1 hn hℓ hpar hν)) ∧
      ∀ g, ∃ a b, blockFrobMap (data_q0 (ℓ := ℓ) hn) a + blockFrobMap (data_q1 hn hℓ hpar hν) b = g := by
  set ε := pairParity c d with hεdef
  have hε : ε = 0 ∨ ε = 1 := pairParity_eq c d
  have hσd := neg_one_pow_sq_fin d.parity
  have h0 := data_q0 (ℓ := ℓ) hn
  have hB := data_B (ℓ := ℓ) hn
  have hD := data_D hn hℓ hpar hν
  have h1 := data_q1 hn hℓ hpar hν
  have e_src0 : GramFormula.realPositionExponent (pre ++ RealBlock.character c :: RealBlock.character d :: post)
      (realRank pre) = c.exponent := by
    rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character d),
      exponent_mid_zero pre post (realRank_cd (c := c) (d := d) ▸ two_pos)]
    rfl
  have e_src1 : GramFormula.realPositionExponent (pre ++ RealBlock.character c :: RealBlock.character d :: post)
      (realRank pre + 1) = d.exponent := by
    rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character d),
      exponent_mid_one pre post (realRank_cd (c := c) (d := d) ▸ one_lt_two)]
    rfl
  have hrecD : IsRecurrent
      (GramFormula.realPositionExponent (pre ++ RealBlock.character c :: RealBlock.character d :: post)
        (realRank pre) -
      GramFormula.realPositionExponent (pre ++ RealBlock.character c :: RealBlock.character d :: post)
        (realRank pre + 1) + 1) ε (tailMultiplier ℓ ε ((-1) ^ d.parity.val)) := by
    rw [e_src0, e_src1, show c.exponent - d.exponent + 1 = 1 - (ℓ : ℂ) by
      linear_combination -hν]
    exact isRecurrent_tailMultiplier hℓ hε hpar hσd
  have hinv : ∀ f, blockFrobMap hD (blockFrobMap h1 f) = f := by
    intro f
    refine blockFrobMap_blockFrobMap_eq h1 hD f fun j hj hne k hk => ?_
    have hP : tailMultiplier ℓ ε ((-1) ^ d.parity.val) j = 0 := by
      by_contra hP
      exact hne (mul_inv_cancel₀ hP)
    have hjl : |j| < ℓ := by
      refine abs_lt_of_parity hpar hj (not_lt.mp fun hlt => ?_)
      exact (tailMultiplier_ne_zero_iff hℓ hε hpar hσd hj).mpr hlt hP
    have hind : realInducedBlockAt (pre ++ indBlock c d ℓ ++ post) (realRank pre) =
        some (pairInduced c d ℓ) := by
      have e := realInducedBlockAt_mid pre (indBlock c d ℓ) post (j := 0) two_pos
      rwa [add_zero] at e
    refine f.2.1.2 (realRank pre) (pairInduced c d ℓ) hind j ?_ k
    rwa [pairInduced_weight, abs_of_nonneg (Int.natCast_nonneg ℓ)]
  have hker : LinearMap.ker (blockFrobMap hD) ≤ LinearMap.range (blockFrobMap h0) := by
    refine ker_le_range h0 hB hD fun j hj hne => ?_
    have hb : binomialMultiplier ℓ ε j = 0 := by
      by_contra hb
      exact hne (mul_inv_cancel₀ hb)
    have hjl : ¬ |j| < ℓ := fun hlt =>
      (binomialMultiplier_ne_zero_iff hℓ hε hpar hj).mpr hlt hb
    refine (tailMultiplier_ne_zero_iff hℓ hε hpar hσd hj).mpr ?_
    rcases (not_lt.mp hjl).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd heq.le (not_le.mpr (abs_lt_of_parity hpar hj heq.symm.le))
  refine ⟨isRealIntertwinerModulo_of_leftInverse h1 hD hrecD hinv _ hker, fun g => ?_⟩
  have hg : g - blockFrobMap h1 (blockFrobMap hD g) ∈ LinearMap.ker (blockFrobMap hD) := by
    rw [LinearMap.mem_ker, map_sub, hinv, sub_self]
  obtain ⟨a, ha⟩ := hker hg
  exact ⟨a, blockFrobMap hD g, by rw [ha, sub_add_cancel]⟩

end Swap

/-! ## The pushforward -/

section Pushforward

open RealStandardFiltration

variable {d : ComplexCharacterData} {c : RealCharacterData} {sa sb : Fin 2}

/-- Every function of the standard module of `[d, c]` is `T₀ (Q₁ h)`. -/
theorem tail_swap_surjective (hl : 0 < d.weight.natAbs)
    (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2) {μ₁ : ℤ → ℂ}
    (hsym₁ : IsSymmetric (pairParity (ca d sa) c) (sigma0 (ca d sa) c) μ₁)
    (hμ₁ : ∀ k, μ₁ k ≠ 0)
    (f : KF 3 ([] ++ [RealBlock.induced d] ++ [RealBlock.character c])) :
    ∃ h, blockFrobMap (data_tail (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs)
      (blockFrobMap (data_swap (pre := [RealBlock.character (cb d sb)]) (post := [])
        (n := 3) rfl hsym₁) h) = f := by
  obtain ⟨g₂, rfl⟩ := tail_surjective (pre := []) (post := [RealBlock.character c]) (n := 3)
    rfl hl hs f
  obtain ⟨g₁, rfl⟩ := swap_surjective (pre := [RealBlock.character (cb d sb)]) (post := [])
    (n := 3) rfl hsym₁ hμ₁ g₂
  exact ⟨g₁, rfl⟩

theorem re_bExp_lt (h : d.exponent.re < c.exponent.re) : 0 < (c.exponent - bExp d).re := by
  simp only [bExp, Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
  have : (0 : ℝ) ≤ (d.weight.natAbs : ℝ) / 2 * 2 / (2 * 2 + 0 * 0) := by positivity
  norm_num at this ⊢
  linarith

/-- **The pushforward, generic case.** If the swap `Q₁` (exponent difference `ν₁ = s - a`) has
nonvanishing denominators and is generic, and the swap `Q₂` (`ν₂ = s - b`, `0 < Re ν₂`) is
generic, the standard module of `[d, c]` has the one-step filtration with piece `[c, d]`. -/
theorem pushforward_generic (hL : RealSwapLandingInducedFirstStatement)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    (hden₁ : ∀ i : ℕ, (pairParity (ca d sa) c : ℂ) + 2 * i + 1 + (c.exponent - aExp d) ≠ 0)
    (hne₁ : ∀ m : ℕ, c.exponent - aExp d ≠ (pairParity (ca d sa) c : ℂ) + 2 * m + 1)
    (hre₂ : 0 < (c.exponent - bExp d).re)
    (hne₂ : ∀ m : ℕ, c.exponent - bExp d ≠ (pairParity (cb d sb) c : ℂ) + 2 * m + 1) :
    RealAdjacentFiltration 3 [] [] (RealBlock.induced d) (RealBlock.character c) := by
  have hε₀ := pairParity_eq (cb d sb) c
  have hε₁ := pairParity_eq (ca d sa) c
  have hsym₀ : IsSymmetric (pairParity (cb d sb) c) (sigma0 (cb d sb) c)
      (genericMultiplier (c.exponent - bExp d) (pairParity (cb d sb) c)) :=
    isSymmetric_genericMultiplier _ hε₀
  have hsym₁ : IsSymmetric (pairParity (ca d sa) c) (sigma0 (ca d sa) c)
      (genericMultiplier (c.exponent - aExp d) (pairParity (ca d sa) c)) :=
    isSymmetric_genericMultiplier _ hε₁
  have hrec₀ := isRecurrent_genericMultiplier hre₂ hε₀
  have hrec₁ := RealCharacterInducedPushforward.isRecurrent_genericMultiplier' hε₁ hden₁
  obtain ⟨L, hLm, hLf⟩ := exists_lift hL hl hs hsym₀ hsym₁ hrec₀ hrec₁
  refine ⟨1, fun _ => [RealBlock.character c, RealBlock.induced d], fun _ => L,
    fun _ => Or.inl rfl, fun _ => modulo_mono hLm bot_le, ?_⟩
  refine eq_top_iff.2 fun f _ => Submodule.mem_iSup_of_mem (0 : Fin 1) ?_
  obtain ⟨h, rfl⟩ := tail_swap_surjective hl hs hsym₁
    (RealCharacterInducedPushforward.genericMultiplier_ne_zero' hden₁ hne₁) f
  obtain ⟨g, rfl⟩ := swap_surjective (pre := []) (post := [RealBlock.character (ca d sa)])
    (n := 3) rfl hsym₀ (genericMultiplier_ne_zero hre₂ hε₀ hne₂) h
  exact ⟨_, hLf g⟩

/-- **The pushforward, reducible case.** If the swap `Q₁` is as in `pushforward_generic` and
`ν₂ = s - b = ℓ` is an integer `ℓ > |m|` with `ℓ - 1 ≡ pairParity c_b c (mod 2)`, the standard
module of `[d, c]` has the two-step filtration with pieces `[c, d]` and
`[induced (pairInduced c_b c ℓ), c_a]`. -/
theorem pushforward_reducible (hL : RealSwapLandingInducedFirstStatement)
    (hl : 0 < d.weight.natAbs) (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)
    (hden₁ : ∀ i : ℕ, (pairParity (ca d sa) c : ℂ) + 2 * i + 1 + (c.exponent - aExp d) ≠ 0)
    (hne₁ : ∀ m : ℕ, c.exponent - aExp d ≠ (pairParity (ca d sa) c : ℂ) + 2 * m + 1)
    {ℓ : ℕ} (hℓl : d.weight.natAbs < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity (cb d sb) c))
    (hν : c.exponent - bExp d = ℓ) :
    RealAdjacentFiltration 3 [] [] (RealBlock.induced d) (RealBlock.character c) := by
  have hε₀ := pairParity_eq (cb d sb) c
  have hε₁ := pairParity_eq (ca d sa) c
  have hℓ : 0 < ℓ := hl.trans hℓl
  have hsym₀ : IsSymmetric (pairParity (cb d sb) c) (sigma0 (cb d sb) c)
      (binomialMultiplier ℓ (pairParity (cb d sb) c)) :=
    isSymmetric_binomialMultiplier ℓ hε₀
  have hsym₁ : IsSymmetric (pairParity (ca d sa) c) (sigma0 (ca d sa) c)
      (genericMultiplier (c.exponent - aExp d) (pairParity (ca d sa) c)) :=
    isSymmetric_genericMultiplier _ hε₁
  have hrec₀ : IsRecurrent (c.exponent - bExp d + 1) (pairParity (cb d sb) c)
      (binomialMultiplier ℓ (pairParity (cb d sb) c)) := by
    rw [hν]
    exact isRecurrent_binomialMultiplier hℓ hε₀ hpar
  have hrec₁ := RealCharacterInducedPushforward.isRecurrent_genericMultiplier' hε₁ hden₁
  obtain ⟨L, hLm, hLf⟩ := exists_lift hL hl hs hsym₀ hsym₁ hrec₀ hrec₁
  have hν' : c.exponent - (cb d sb).exponent = ℓ := hν
  obtain ⟨hq1, hspan⟩ := reducible_pieces (pre := []) (post := [RealBlock.character (ca d sa)])
    (n := 3) rfl hℓ hpar hν'
  set T₀ := data_tail (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs
  set Q₁ := data_swap (pre := [RealBlock.character (cb d sb)]) (post := []) (n := 3) rfl hsym₁
  set q₁ := data_q1 (pre := []) (post := [RealBlock.character (ca d sa)]) (n := 3) rfl hℓ hpar hν'
  have hT₀Q₁ : IsRealIntertwinerModulo 3 _ _ ⊥ (blockFrobMap T₀ ∘ₗ blockFrobMap Q₁) :=
    modulo_comp_bot (modulo_tail (pre := []) (post := [RealBlock.character c]) (n := 3) rfl hl hs)
      (isRealIntertwinerModulo_blockFrobMap Q₁
        (by rw [exponent_swp_zero, exponent_swp_one]; exact hrec₁) ⊥)
  let P := (blockFrobMap T₀ ∘ₗ blockFrobMap Q₁) ∘ₗ blockFrobMap q₁
  have hP : IsRealIntertwinerModulo 3 _ _ (LinearMap.range L) P := by
    refine modulo_mono (modulo_comp hT₀Q₁ hq1) (sup_le bot_le ?_)
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨_, hLf g⟩
  let ws : Fin 2 → List RealBlock := ![[RealBlock.character c, RealBlock.induced d],
    [RealBlock.induced (pairInduced (cb d sb) c ℓ), RealBlock.character (ca d sa)]]
  let q : ∀ j : Fin 2,
      KF 3 ([] ++ ws j ++ []) →ₗ[ℂ] KF 3 ([] ++ RealBlock.induced d :: RealBlock.character c :: []) :=
    Fin.cons (α := fun j : Fin 2 =>
      KF 3 ([] ++ ws j ++ []) →ₗ[ℂ] KF 3 ([] ++ RealBlock.induced d :: RealBlock.character c :: []))
      L (Fin.cons P finZeroElim)
  refine ⟨2, ws, q, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, ?_⟩
      · show (realExponentSupport ([RealBlock.induced (pairInduced (cb d sb) c ℓ)] ++
          [RealBlock.character (ca d sa)])).Perm _
        rw [realExponentSupport, List.flatMap_append, ← realExponentSupport,
          realExponentSupport_pairInduced_eq hν']
        show [c.exponent, bExp d, aExp d].Perm [aExp d, bExp d, c.exponent]
        exact List.reverse_perm [aExp d, bExp d, c.exponent]
      · simp only [ws, realWeightSquareSum, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, realBlockWeightSquare, add_zero]
        exact Nat.pow_lt_pow_left hℓl two_ne_zero
  · intro j
    fin_cases j
    · exact modulo_mono hLm bot_le
    · refine modulo_mono hP ?_
      exact le_iSup₂_of_le (f := fun (i : Fin 2) (_ : i < 1) => LinearMap.range (q i))
        (0 : Fin 2) (by decide) le_rfl
  · refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨h, rfl⟩ := tail_swap_surjective hl hs hsym₁
      (RealCharacterInducedPushforward.genericMultiplier_ne_zero' hden₁ hne₁) f
    obtain ⟨a, b, rfl⟩ := hspan h
    have m0 : L (blockFrobMap (data_tail (pre := [RealBlock.character c]) (post := []) (n := 3)
        rfl hl hs) a) ∈ ⨆ j, LinearMap.range (q j) :=
      Submodule.mem_iSup_of_mem (0 : Fin 2) ⟨_, rfl⟩
    have m1 : P b ∈ ⨆ j, LinearMap.range (q j) :=
      Submodule.mem_iSup_of_mem (1 : Fin 2) ⟨b, rfl⟩
    rw [map_add, map_add, ← hLf a]
    exact add_mem m0 m1

end Pushforward

end RealInducedCharacter

end Langlands.Archimedean
