import Langlands.Representation.Archimedean.RealCharacterInducedPushforward
import Langlands.Representation.Archimedean.RealKTypeTransport
import Langlands.Representation.Archimedean.RealOrthogonalUncertaintyStatement
import Langlands.Representation.Archimedean.RealSwapLandingStatement

/-!
# The filtration for a character and an induction block by an isomorphism

Let `c = sgn^ε |·|^s` be a real character and `d` a complex character of weight `m ≠ 0` and
exponent `t`, `ℓ = |m|`, `a = t + ℓ/2`, `b = t - ℓ/2`. Suppose `b - s = -m₀` for an integer
`0 < m₀ < ℓ`. This file shows that the `O(3)`-finite functions of the standard modules of
`[c, d]` and `[d, c]` are isomorphic by an exact intertwiner, so that `[c, d]` has the adjacent
filtration with the single piece `[d, c]`:

* `m₀ + ε` odd: the composite `T = A₀ ∘ A₁ : K([d, c]) → K([c, d])` of a tail map `A₁`
  along `r₁` and a generic swap `A₀` along `r₀` (`filtration_tail_first`);
* `m₀ + ε` even: the composite `E = B₁ ∘ B₀ : K([c, d]) → K([d, c])` of a tail map `B₀` along
  `r₀` and a generic swap `B₁` along `r₁`, inverted (`filtration_tail_second`).

The composites land in the standard modules by the landing statements, are injective by the
uncertainty statement, and are onto by the `K`-type count of `RealKTypeTransport`.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealCharacterInducedSwap

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealCharacterPairReducible RealBlockJacquet RealStandardFiltration
open RealCharacterInducedPushforward
open Langlands.LocalFactor.Archimedean

/-! ## General lemmas -/

section General

variable {n : ℕ}

/-- A Frobenius map whose multiplier has no zeros on the parity class is injective. -/
theorem frob_injective_of_ne_zero {ds es : List RealBlock} {p : ℕ} {ε : ℤ} {σ : ℂ}
    {μ : ℤ → ℂ} (h : IsBlockFrobData n ds es p ε σ μ)
    (h0 : ∀ k : ℤ, Even (k - ε) → μ k ≠ 0) : Function.Injective (blockFrobMap h) := by
  refine (injective_iff_map_eq_zero _).mpr fun g hg => ?_
  refine eq_of_blockFourierCoefficient_eq h.lt fun j x hx => ?_
  rw [ZeroMemClass.coe_zero, blockFourierCoefficient_zero]
  by_cases hj : Even (j - ε)
  · have e := blockFourierCoefficient_blockFrobMap h g hx j
    rw [hg, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (h0 j hj)
  · exact blockFourierCoefficient_eq_zero_of_not_even h.lt h.par g hj x

/-- If the tail map with multiplier `tailMultiplier ℓ ε σ` kills `g`, the modes `|j| ≥ ℓ` of
`g` along the block vanish on `O(n)`. -/
theorem modes_of_tail_eq_zero {ds es : List RealBlock} {p : ℕ} {ε : ℤ} {σ σ' : ℂ} {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε)) (hσ : σ ^ 2 = 1)
    (h : IsBlockFrobData n ds es p ε σ' (tailMultiplier ℓ ε σ)) (g : KF n ds)
    (hg : blockFrobMap h g = 0) :
    ∀ x ∈ unitaryCompact ℝ n, ∀ j : ℤ, (ℓ : ℤ) ≤ |j| →
      blockFourierCoefficient n p j (g : Langlands.GeneralLinear n ℝ → ℂ) x = 0 := by
  intro x hx j hj
  by_cases hje : Even (j - ε)
  · have e := blockFourierCoefficient_blockFrobMap h g hx j
    rw [hg, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at e
    refine (mul_eq_zero.mp e.symm).resolve_left
      ((tailMultiplier_ne_zero_iff hℓ hε hpar hσ hje).mpr ?_)
    rcases hj.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd heq.le (not_le.mpr (abs_lt_of_parity hpar hje heq.symm.le))
  · exact blockFourierCoefficient_eq_zero_of_not_even h.lt h.par g hje x

/-- An `O(n)`-finite function of a standard module that vanishes on `O(n)` is zero. -/
theorem eq_zero_of_unitaryCompact {ds : List RealBlock} (f : KF n ds)
    (hf : ∀ g ∈ unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) g = 0) : f = 0 := by
  apply Subtype.ext
  exact eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2.1.1 (Submodule.zero_mem _)
    fun g hg => by rw [hf g hg]; rfl

/-- A linear map with the same underlying functions as an exact intertwiner is an exact
intertwiner. -/
theorem modulo_bot_of_coe {ds es fs : List RealBlock} {q : KF n ds →ₗ[ℂ] KF n es}
    {q' : KF n ds →ₗ[ℂ] KF n fs} (hq : IsRealIntertwinerModulo n ds es ⊥ q)
    (hcoe : ∀ f, (q' f : Langlands.GeneralLinear n ℝ → ℂ) = q f) :
    IsRealIntertwinerModulo n ds fs ⊥ q' := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hg, h⟩ := hq.1 k f
    refine ⟨hf, rightTranslation_mem_kFiniteFunctions_realStandardModule n fs (q' f).2 k.2, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at h ⊢
    apply Subtype.ext
    change (q' ⟨_, hf⟩ : Langlands.GeneralLinear n ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) (k : Langlands.GeneralLinear n ℝ)
        (q' f : Langlands.GeneralLinear n ℝ → ℂ)
    rw [hcoe ⟨_, hf⟩, hcoe f]
    exact congrArg Subtype.val h
  · obtain ⟨hf, hg, h⟩ := hq.2 X f
    refine ⟨hf, rightDerivative_mem_kFiniteFunctions_realStandardModule n fs (q' f).2 X, ?_⟩
    rw [Submodule.mem_bot, sub_eq_zero] at h ⊢
    apply Subtype.ext
    change (q' ⟨_, hf⟩ : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) X (q' f : Langlands.GeneralLinear n ℝ → ℂ)
    rw [hcoe ⟨_, hf⟩, hcoe f]
    exact congrArg Subtype.val h

/-- The inverse of a bijective exact intertwiner is an exact intertwiner. -/
theorem modulo_symm {ds es : List RealBlock} {E : KF n ds →ₗ[ℂ] KF n es}
    (hE : IsRealIntertwinerModulo n ds es ⊥ E) (hb : Function.Bijective E) :
    IsRealIntertwinerModulo n es ds ⊥ (LinearEquiv.ofBijective E hb).symm.toLinearMap :=
  modulo_of_comp_surjective (modulo_id ds) hE hb.2
    (LinearMap.ext fun f => (LinearEquiv.ofBijective E hb).symm_apply_apply f)

end General

/-! ## The lists -/

section Setup

variable (c : RealCharacterData) (d : ComplexCharacterData)

/-- `χ_A = sgn^{ℓ+1} |·|^a`, the first position character of `d`. -/
def chA : RealCharacterData :=
  RealJacquetFrobenius.charData (fin2 (d.weight.natAbs + 1))
    (d.exponent + (d.weight.natAbs : ℂ) / 2)

/-- `χ_B = |·|^b`, the second position character of `d`. -/
def chB : RealCharacterData :=
  RealJacquetFrobenius.charData 0 (d.exponent - (d.weight.natAbs : ℂ) / 2)

theorem chA_exponent : (chA d).exponent = d.exponent + (d.weight.natAbs : ℂ) / 2 := rfl

theorem chB_exponent : (chB d).exponent = d.exponent - (d.weight.natAbs : ℂ) / 2 := rfl

/-- `[c, d]`. -/
abbrev lCD : List RealBlock := [RealBlock.character c, RealBlock.induced d]

/-- `[d, c]`. -/
abbrev lDC : List RealBlock := [RealBlock.induced d, RealBlock.character c]

/-- `M = [χ_A, c, χ_B]`. -/
abbrev lM : List RealBlock :=
  [RealBlock.character (chA d), RealBlock.character c, RealBlock.character (chB d)]

/-- `P = [c, χ_A, χ_B]`, whose standard module contains that of `[c, d]`. -/
abbrev lP : List RealBlock :=
  [RealBlock.character c, RealBlock.character (chA d), RealBlock.character (chB d)]

/-- `Q = [χ_A, χ_B, c]`, whose standard module contains that of `[d, c]`. -/
abbrev lQ : List RealBlock :=
  [RealBlock.character (chA d), RealBlock.character (chB d), RealBlock.character c]

theorem posExp_lDC_1 : GramFormula.realPositionExponent (lDC c d) 1 =
    d.exponent - (d.weight.natAbs : ℂ) / 2 := rfl

theorem posExp_lDC_2 : GramFormula.realPositionExponent (lDC c d) (1 + 1) =
    c.exponent := rfl

theorem posExp_lCD_0 : GramFormula.realPositionExponent (lCD c d) 0 = c.exponent := rfl

theorem posExp_lCD_1 : GramFormula.realPositionExponent (lCD c d) (0 + 1) =
    d.exponent + (d.weight.natAbs : ℂ) / 2 := rfl

theorem posExp_lM_0 : GramFormula.realPositionExponent (lM c d) 0 = (chA d).exponent :=
  rfl

theorem posExp_lM_1 : GramFormula.realPositionExponent (lM c d) (0 + 1) = c.exponent :=
  rfl

theorem posExp_lM_1' : GramFormula.realPositionExponent (lM c d) 1 = c.exponent := rfl

theorem posExp_lM_2 : GramFormula.realPositionExponent (lM c d) (1 + 1) =
    (chB d).exponent := rfl

theorem posChar_lP : realPositionCharacter (lP c d) = realPositionCharacter (lCD c d) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | i <;> rfl

theorem posChar_lQ : realPositionCharacter (lQ c d) = realPositionCharacter (lDC c d) := by
  funext i x
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun]
  rcases i with _ | _ | _ | i <;> rfl

/-- A function of the standard module of `P` whose modes `|k| < ℓ` along `r₁` vanish on
`O(3)` lies in the standard module of `[c, d]`. -/
theorem mem_lCD (f : KF 3 (lP c d))
    (hK : ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 1 k (f : Langlands.GeneralLinear 3 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ KF 3 (lCD c d) := by
  refine ⟨mem_realStandardModule_of_unitaryCompact (N := 3) (ds := lCD c d) rfl ?_
    fun p d₀ hd k hk g hg => ?_, f.2.2⟩
  · rw [← posChar_lP]
    exact f.2.1.1
  · obtain ⟨rfl, rfl⟩ := RealSwapFLanding.realInducedBlockAt_character_induced c d hd
    exact hK g hg k hk

/-- A function of the standard module of `Q` whose modes `|k| < ℓ` along `r₀` vanish on
`O(3)` lies in the standard module of `[d, c]`. -/
theorem mem_lDC (f : KF 3 (lQ c d))
    (hK : ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 0 k (f : Langlands.GeneralLinear 3 ℝ → ℂ) g = 0) :
    (f : Langlands.GeneralLinear 3 ℝ → ℂ) ∈ KF 3 (lDC c d) := by
  refine ⟨mem_realStandardModule_of_unitaryCompact (N := 3) (ds := lDC c d) rfl ?_
    fun p d₀ hd k hk g hg => ?_, f.2.2⟩
  · rw [← posChar_lQ]
    exact f.2.1.1
  · obtain ⟨rfl, rfl⟩ := realInducedBlockAt_induced_character c d hd
    exact hK g hg k hk

/-- A surjective exact intertwiner from `K([d, c])` onto `K([c, d])` gives the adjacent
filtration of `[c, d]` with the single piece `[d, c]`. -/
theorem filtration_of_surjective (T : KF 3 (lDC c d) →ₗ[ℂ] KF 3 (lCD c d))
    (hT : IsRealIntertwinerModulo 3 (lDC c d) (lCD c d) ⊥ T) (hTs : Function.Surjective T) :
    RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d) := by
  refine (realAdjacentFiltration_iff 3 [] [] _ _).mpr ?_
  refine ((HasFiltration.self (P := fun es => es = lDC c d) rfl).map T hT hTs).mono ?_
  rintro es rfl
  exact piece_W c d

end Setup

/-! ## The Frobenius data -/

section Data

variable (c : RealCharacterData) (d : ComplexCharacterData)

/-- `A₁ : K([d, c]) → K(M)` along the block `1, 2`, which straddles the induction block. -/
theorem dataA1 {σ : ℂ} {μ : ℤ → ℂ} (hσ : σ = (-1) ^ c.parity.val)
    (hs : IsSymmetric (c.parity.val : ℤ) σ μ) :
    IsBlockFrobData 3 (lDC c d) (lM c d) 1 (c.parity.val : ℤ) σ μ where
  lt := by norm_num
  rank := rfl
  sign_off i h1 h2 := by
    rcases i with _ | _ | _ | i
    · rfl
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rfl
  exp_off i h1 h2 := by
    rcases i with _ | _ | _ | i
    · rfl
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rfl
  exp_p := rfl
  exp_q := rfl
  par := by
    rw [zpow_natCast, realPositionCharacter_neg_one, realPositionCharacter_neg_one]
    change (-1 : ℂ) ^ c.parity.val = (-1) ^ (0 : Fin 2).val * (-1) ^ c.parity.val
    rw [Fin.val_zero, pow_zero, one_mul]
  sym := hs
  sign_p := by
    rw [realPositionCharacter_neg_one, hσ]
    change (-1 : ℂ) ^ c.parity.val = (-1) ^ (0 : Fin 2).val * (-1) ^ c.parity.val
    rw [Fin.val_zero, pow_zero, one_mul]
  sign_q := by
    rw [realPositionCharacter_neg_one, hσ]
    change (-1 : ℂ) ^ (0 : Fin 2).val = (-1) ^ c.parity.val * (-1) ^ c.parity.val
    rw [Fin.val_zero, pow_zero, ← sq, neg_one_pow_sq_fin]
  induced_off i d' _ hd := by
    rcases i with _ | _ | _ | i <;> simp [realInducedBlockAt] at hd
  induced_p d' hd := by simp [realInducedBlockAt] at hd

/-- `A₀ : K(M) → K(P)`, the swap of `χ_A` and `c` along the block `0, 1`. -/
theorem dataA0 {μ : ℤ → ℂ} (hs : IsSymmetric (pairParity c (chA d)) (sigma0 c (chA d)) μ) :
    IsBlockFrobData 3 (lM c d) (lP c d) 0 (pairParity c (chA d)) (sigma0 c (chA d)) μ :=
  data_swap (pre := []) (post := [RealBlock.character (chB d)]) (c := c) (d := chA d) rfl hs

/-- `B₀ : K([c, d]) → K(M)` along the block `0, 1`, which straddles the induction block. -/
theorem dataB0 {μ : ℤ → ℂ} (hs : IsSymmetric (pairParity c (chA d)) (sigma0 c (chA d)) μ) :
    IsBlockFrobData 3 (lCD c d) (lM c d) 0 (pairParity c (chA d)) (sigma0 c (chA d)) μ where
  lt := by norm_num
  rank := rfl
  sign_off i h1 h2 := by
    rcases i with _ | _ | _ | i
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rfl
    · rfl
  exp_off i h1 h2 := by
    rcases i with _ | _ | _ | i
    · exact absurd rfl h1
    · exact absurd rfl h2
    · rfl
    · rfl
  exp_p := rfl
  exp_q := rfl
  par := by
    rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one, neg_one_pow_pairParity']
    rfl
  sym := hs
  sign_p := by
    rw [realPositionCharacter_neg_one, sigma0_eq]
    change (-1 : ℂ) ^ (chA d).parity.val =
      (-1) ^ c.parity.val * ((-1) ^ c.parity.val * (-1) ^ (chA d).parity.val)
    linear_combination (-(-1 : ℂ) ^ (chA d).parity.val) * neg_one_pow_sq_fin c.parity
  sign_q := by
    rw [realPositionCharacter_neg_one, sigma0_eq]
    change (-1 : ℂ) ^ c.parity.val =
      (-1) ^ (chA d).parity.val * ((-1) ^ c.parity.val * (-1) ^ (chA d).parity.val)
    linear_combination (-(-1 : ℂ) ^ c.parity.val) * neg_one_pow_sq_fin (chA d).parity
  induced_off i d' _ hd := by
    rcases i with _ | _ | _ | i <;> simp [realInducedBlockAt] at hd
  induced_p d' hd := by simp [realInducedBlockAt] at hd

/-- `B₁ : K(M) → K(Q)`, the swap of `c` and `χ_B` along the block `1, 2`. -/
theorem dataB1 {μ : ℤ → ℂ} (hs : IsSymmetric (pairParity (chB d) c) (sigma0 (chB d) c) μ) :
    IsBlockFrobData 3 (lM c d) (lQ c d) 1 (pairParity (chB d) c) (sigma0 (chB d) c) μ :=
  data_swap (pre := [RealBlock.character (chA d)]) (post := []) (c := chB d) (d := c) rfl hs

end Data

/-! ## The two cases -/

section Cases

variable (c : RealCharacterData) (d : ComplexCharacterData)

theorem parity_cases : ((c.parity.val : ℕ) : ℤ) = 0 ∨ ((c.parity.val : ℕ) : ℤ) = 1 := by
  have := c.parity.isLt
  omega

theorem pairParity_c_chA :
    pairParity c (chA d) = (((c.parity.val + (d.weight.natAbs + 1) % 2) % 2 : ℕ) : ℤ) := rfl

theorem natAbs_pairParity_c_chA :
    (pairParity c (chA d)).natAbs = (c.parity.val + (d.weight.natAbs + 1) % 2) % 2 := rfl

theorem pairParity_chB_c : pairParity (chB d) c = (((0 + c.parity.val) % 2 : ℕ) : ℤ) := rfl

theorem natAbs_pairParity_chB_c : (pairParity (chB d) c).natAbs = (0 + c.parity.val) % 2 := rfl

/-- The class of `c, χ_A` is that of `ℓ + 1 + ε`. -/
theorem even_class_c_chA :
    Even (pairParity c (chA d) - ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)) := by
  rw [pairParity_c_chA, Int.even_iff]
  omega

theorem sign_class_c_chA :
    (-1 : ℂ) ^ (pairParity c (chA d)).natAbs = (-1) ^ (d.weight.natAbs + 1 + c.parity.val) := by
  rw [natAbs_pairParity_c_chA]
  exact neg_one_pow_congr (by omega)

/-- The class of `χ_B, c` is that of `ε`. -/
theorem even_class_chB_c : Even (pairParity (chB d) c - (c.parity.val : ℤ)) := by
  rw [pairParity_chB_c, Int.even_iff]
  omega

theorem sign_class_chB_c :
    (-1 : ℂ) ^ (pairParity (chB d) c).natAbs = (-1) ^ c.parity.val := by
  rw [natAbs_pairParity_chB_c]
  exact neg_one_pow_congr (by omega)

/-- **Case (c), `m₀ + ε` odd.** Assume the landing statement from `[d, c]` and the
uncertainty statement. If `ℓ > 0`, `b - s = -m₀` with `0 < m₀ < ℓ` and `m₀ + ε` odd, then
`[c, d]` has the adjacent filtration with the single piece `[d, c]`. -/
theorem filtration_tail_first (hLI : RealSwapLandingInducedFirstStatement)
    (hU : RealOrthogonalBlockUncertaintyStatement) {m : ℕ} (hm0 : 0 < m)
    (hml : m < d.weight.natAbs) (hw : (chB d).exponent - c.exponent = -(m : ℂ))
    (hpar : (m + c.parity.val) % 2 = 1) :
    RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d) := by
  have hw' : d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = -(m : ℂ) := hw
  have hε := parity_cases c
  have hparT : Even ((m : ℤ) - 1 - (c.parity.val : ℤ)) := by
    rw [Int.even_iff]
    omega
  have hσ : ((-1 : ℂ) ^ c.parity.val) ^ 2 = 1 := neg_one_pow_sq_fin c.parity
  -- the tail map `A₁` along `r₁`
  have hs₁ := isSymmetric_tailMultiplier hm0 hε hparT hσ
  have hA1 := dataA1 c d rfl hs₁
  have hrec₁ : IsRecurrent (1 - (m : ℂ)) (c.parity.val : ℤ)
      (tailMultiplier m (c.parity.val : ℤ) ((-1) ^ c.parity.val)) :=
    isRecurrent_tailMultiplier hm0 hε hparT hσ
  have hA1m : IsRealIntertwinerModulo 3 (lDC c d) (lM c d) ⊥ (blockFrobMap hA1) := by
    refine isRealIntertwinerModulo_blockFrobMap hA1 ?_ ⊥
    rw [posExp_lDC_1, posExp_lDC_2,
      show d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent + 1 = 1 - (m : ℂ) by
        linear_combination hw']
    exact hrec₁
  -- the generic swap `A₀` along `r₀`, with `ν₀ = a - s = ℓ - m₀`
  have hν₀ : (chA d).exponent - c.exponent = ((d.weight.natAbs - m : ℕ) : ℂ) := by
    rw [Nat.cast_sub hml.le, chA_exponent]
    linear_combination hw'
  have hν₀re : 0 < (((d.weight.natAbs - m : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast Nat.sub_pos_of_lt hml
  have hε₀ := pairParity_eq c (chA d)
  have hs₀ := isSymmetric_genericMultiplier ((d.weight.natAbs - m : ℕ) : ℂ) hε₀
  have hA0 := dataA0 c d hs₀
  have hrec₀ : IsRecurrent (((d.weight.natAbs - m : ℕ) : ℂ) + 1) (pairParity c (chA d))
      (genericMultiplier ((d.weight.natAbs - m : ℕ) : ℂ) (pairParity c (chA d))) :=
    isRecurrent_genericMultiplier hν₀re hε₀
  have hA0m : IsRealIntertwinerModulo 3 (lM c d) (lP c d) ⊥ (blockFrobMap hA0) := by
    refine isRealIntertwinerModulo_blockFrobMap hA0 ?_ ⊥
    rw [posExp_lM_0, posExp_lM_1, hν₀]
    exact hrec₀
  have hA0i : Function.Injective (blockFrobMap hA0) :=
    frob_injective_of_ne_zero hA0 fun k _ => genericMultiplier_ne_zero hν₀re hε₀ (fun i h => by
      have e : ((d.weight.natAbs - m : ℕ) : ℤ) = pairParity c (chA d) + 2 * i + 1 := by
        exact_mod_cast h
      rw [pairParity_c_chA] at e
      omega) k
  -- the composite lands in the standard module of `[c, d]`
  have hrec₀' : IsRecurrent (1 - (m : ℂ) + (d.weight.natAbs : ℂ))
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      (genericMultiplier ((d.weight.natAbs - m : ℕ) : ℂ) (pairParity c (chA d))) := by
    rw [show 1 - (m : ℂ) + (d.weight.natAbs : ℂ) = ((d.weight.natAbs - m : ℕ) : ℂ) + 1 by
      rw [Nat.cast_sub hml.le]
      ring]
    exact isRecurrent_of_even hrec₀ (even_class_c_chA c d)
  have hland : ∀ f : KF 3 (lDC c d), ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 1 k
        ((blockFrobMap hA0 (blockFrobMap hA1 f) : KF 3 (lP c d)) :
          Langlands.GeneralLinear 3 ℝ → ℂ) g = 0 := fun f =>
    hLI c d (1 - (m : ℂ)) _ _ (f : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hA1 f : KF 3 (lM c d)) : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hA0 (blockFrobMap hA1 f) : KF 3 (lP c d)) :
        Langlands.GeneralLinear 3 ℝ → ℂ)
      hrec₁ hs₁ hrec₀' (isSymmetric_of_even hs₀ (even_class_c_chA c d) (sign_class_c_chA c d))
      f.2 (continuous_coe _) (continuous_coe _)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hA1 f hg k)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hA0 _ hg k)
  let T1 : KF 3 (lDC c d) →ₗ[ℂ] KF 3 (lP c d) := blockFrobMap hA0 ∘ₗ blockFrobMap hA1
  let T : KF 3 (lDC c d) →ₗ[ℂ] KF 3 (lCD c d) :=
    LinearMap.codRestrict (KF 3 (lCD c d)) ((KF 3 (lP c d)).subtype ∘ₗ T1)
      (fun f => mem_lCD c d (T1 f) (hland f))
  have hT : IsRealIntertwinerModulo 3 (lDC c d) (lCD c d) ⊥ T :=
    modulo_bot_of_coe (modulo_comp_bot hA0m hA1m) (fun _ => rfl)
  -- `T` is injective by the uncertainty principle
  have hTi : Function.Injective T := by
    refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
    have h1 : blockFrobMap hA0 (blockFrobMap hA1 f) = 0 := by
      apply Subtype.ext
      have h0 := congrArg Subtype.val hf
      exact h0
    have h2 : blockFrobMap hA1 f = 0 := hA0i (by rw [map_zero]; exact h1)
    have hhigh := modes_of_tail_eq_zero hm0 hε hparT hσ hA1 f h2
    exact eq_zero_of_unitaryCompact f (hU 0 1 d.weight.natAbs m f (Or.inl ⟨rfl, rfl⟩) hml
      (continuous_coe f) f.2.2
      (fun g _ j hj => f.2.1.2 0 d rfl j (by rw [Int.abs_eq_natAbs d.weight]; exact hj) g)
      (fun g hg j hj => hhigh g hg j hj))
  have hTs : Function.Surjective T :=
    RealKTypeTransport.surjective_of_injective_induced_character c d hT.isRealKEquivariant hTi
  exact filtration_of_surjective c d T hT hTs

/-- **Case (c), `m₀ + ε` even.** Assume the landing statement from `[c, d]` and the
uncertainty statement. If `ℓ > 0`, `b - s = -m₀` with `0 < m₀ < ℓ` and `m₀ + ε` even, then
`[c, d]` has the adjacent filtration with the single piece `[d, c]`. -/
theorem filtration_tail_second (hLC : RealSwapLandingCharacterFirstStatement)
    (hU : RealOrthogonalBlockUncertaintyStatement) {m : ℕ} (hm0 : 0 < m)
    (hml : m < d.weight.natAbs) (hw : (chB d).exponent - c.exponent = -(m : ℂ))
    (hpar : (m + c.parity.val) % 2 = 0) :
    RealAdjacentFiltration 3 [] [] (RealBlock.character c) (RealBlock.induced d) := by
  have hw' : d.exponent - (d.weight.natAbs : ℂ) / 2 - c.exponent = -(m : ℂ) := hw
  have hε₀ := pairParity_eq c (chA d)
  have hl0 : 0 < d.weight.natAbs - m := Nat.sub_pos_of_lt hml
  have hparT : Even (((d.weight.natAbs - m : ℕ) : ℤ) - 1 - pairParity c (chA d)) := by
    rw [pairParity_c_chA, Int.even_iff]
    omega
  have hσ₀ : (sigma0 c (chA d)) ^ 2 = 1 := by
    rw [sigma0_eq, mul_pow, neg_one_pow_sq_fin, neg_one_pow_sq_fin, one_mul]
  -- the tail map `B₀` along `r₀`
  have hs₀ := isSymmetric_tailMultiplier hl0 hε₀ hparT hσ₀
  have hB0 := dataB0 c d hs₀
  have hrec₀ : IsRecurrent (1 - ((d.weight.natAbs - m : ℕ) : ℂ)) (pairParity c (chA d))
      (tailMultiplier (d.weight.natAbs - m) (pairParity c (chA d)) (sigma0 c (chA d))) :=
    isRecurrent_tailMultiplier hl0 hε₀ hparT hσ₀
  have hB0m : IsRealIntertwinerModulo 3 (lCD c d) (lM c d) ⊥ (blockFrobMap hB0) := by
    refine isRealIntertwinerModulo_blockFrobMap hB0 ?_ ⊥
    rw [posExp_lCD_0, posExp_lCD_1,
      show c.exponent - (d.exponent + (d.weight.natAbs : ℂ) / 2) + 1 =
          1 - ((d.weight.natAbs - m : ℕ) : ℂ) by
        rw [Nat.cast_sub hml.le]
        linear_combination -hw']
    exact hrec₀
  -- the generic swap `B₁` along `r₁`, with `ν₁ = s - b = m₀`
  have hε₁ := pairParity_eq (chB d) c
  have hν₁re : 0 < ((m : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast hm0
  have hs₁ := isSymmetric_genericMultiplier (m : ℂ) hε₁
  have hB1 := dataB1 c d hs₁
  have hrec₁ : IsRecurrent ((m : ℂ) + 1) (pairParity (chB d) c)
      (genericMultiplier (m : ℂ) (pairParity (chB d) c)) :=
    isRecurrent_genericMultiplier hν₁re hε₁
  have hB1m : IsRealIntertwinerModulo 3 (lM c d) (lQ c d) ⊥ (blockFrobMap hB1) := by
    refine isRealIntertwinerModulo_blockFrobMap hB1 ?_ ⊥
    rw [posExp_lM_1', posExp_lM_2,
      show c.exponent - (chB d).exponent + 1 = (m : ℂ) + 1 by linear_combination -hw]
    exact hrec₁
  have hB1i : Function.Injective (blockFrobMap hB1) :=
    frob_injective_of_ne_zero hB1 fun k _ => genericMultiplier_ne_zero hν₁re hε₁ (fun i h => by
      have e : (m : ℤ) = pairParity (chB d) c + 2 * i + 1 := by exact_mod_cast h
      rw [pairParity_chB_c] at e
      omega) k
  -- the composite lands in the standard module of `[d, c]`
  have hrec₁' : IsRecurrent (1 - ((d.weight.natAbs - m : ℕ) : ℂ) + (d.weight.natAbs : ℂ))
      (c.parity.val : ℤ) (genericMultiplier (m : ℂ) (pairParity (chB d) c)) := by
    rw [show 1 - ((d.weight.natAbs - m : ℕ) : ℂ) + (d.weight.natAbs : ℂ) = (m : ℂ) + 1 by
      rw [Nat.cast_sub hml.le]
      ring]
    exact isRecurrent_of_even hrec₁ (even_class_chB_c c d)
  have hland : ∀ f : KF 3 (lCD c d), ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 0 k
        ((blockFrobMap hB1 (blockFrobMap hB0 f) : KF 3 (lQ c d)) :
          Langlands.GeneralLinear 3 ℝ → ℂ) g = 0 := fun f =>
    hLC c d (1 - ((d.weight.natAbs - m : ℕ) : ℂ)) _ _ (f : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hB0 f : KF 3 (lM c d)) : Langlands.GeneralLinear 3 ℝ → ℂ)
      ((blockFrobMap hB1 (blockFrobMap hB0 f) : KF 3 (lQ c d)) :
        Langlands.GeneralLinear 3 ℝ → ℂ)
      (isRecurrent_of_even hrec₀ (even_class_c_chA c d))
      (isSymmetric_of_even hs₀ (even_class_c_chA c d) (sign_class_c_chA c d))
      hrec₁' (isSymmetric_of_even hs₁ (even_class_chB_c c d) (sign_class_chB_c c d))
      f.2 (continuous_coe _) (continuous_coe _)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hB0 f hg k)
      (fun g hg k => blockFourierCoefficient_blockFrobMap hB1 _ hg k)
  let E1 : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lQ c d) := blockFrobMap hB1 ∘ₗ blockFrobMap hB0
  let E : KF 3 (lCD c d) →ₗ[ℂ] KF 3 (lDC c d) :=
    LinearMap.codRestrict (KF 3 (lDC c d)) ((KF 3 (lQ c d)).subtype ∘ₗ E1)
      (fun f => mem_lDC c d (E1 f) (hland f))
  have hE : IsRealIntertwinerModulo 3 (lCD c d) (lDC c d) ⊥ E :=
    modulo_bot_of_coe (modulo_comp_bot hB1m hB0m) (fun _ => rfl)
  -- `E` is injective by the uncertainty principle
  have hEi : Function.Injective E := by
    refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
    have h1 : blockFrobMap hB1 (blockFrobMap hB0 f) = 0 := by
      apply Subtype.ext
      have h0 := congrArg Subtype.val hf
      exact h0
    have h2 : blockFrobMap hB0 f = 0 := hB1i (by rw [map_zero]; exact h1)
    have hhigh := modes_of_tail_eq_zero hl0 hε₀ hparT hσ₀ hB0 f h2
    exact eq_zero_of_unitaryCompact f (hU 1 0 d.weight.natAbs (d.weight.natAbs - m) f
      (Or.inr ⟨rfl, rfl⟩) (Nat.sub_lt (by omega) hm0) (continuous_coe f) f.2.2
      (fun g _ j hj => f.2.1.2 1 d rfl j (by rw [Int.abs_eq_natAbs d.weight]; exact hj) g)
      (fun g hg j hj => hhigh g hg j hj))
  have hEs : Function.Surjective E :=
    RealKTypeTransport.surjective_of_injective_character_induced c d hE.isRealKEquivariant hEi
  have hb : Function.Bijective E := ⟨hEi, hEs⟩
  exact filtration_of_surjective c d (LinearEquiv.ofBijective E hb).symm.toLinearMap
    (modulo_symm hE hb) (LinearEquiv.ofBijective E hb).symm.surjective

end Cases

end RealCharacterInducedSwap

end Langlands.Archimedean
