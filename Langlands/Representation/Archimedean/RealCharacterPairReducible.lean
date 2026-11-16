import Langlands.Representation.Archimedean.RealBlockFrobeniusMap
import Langlands.Representation.Archimedean.RealCharacterPairData

/-!
# The filtration for two real characters in the reducible case

Let `c, d` be real characters with exponents `t_c, t_d` such that `t_d - t_c = ℓ` is a positive
integer with `ℓ - 1 ≡ ε (mod 2)`, where `ε = pairParity c d`. Write
`src = pre ++ c :: d :: post`, `swp = pre ++ [d, c] ++ post` and
`ind = pre ++ [induced (pairInduced c d ℓ)] ++ post`. This file constructs the filtration
`RealAdjacentFiltration n pre post c d` with two pieces:

* `q₀ : K(swp) → K(src)`, the Frobenius map with the binomial multiplier (an intertwiner);
* `q₁ : K(ind) → K(src)`, the Frobenius map with the inverse of the tail multiplier, which is
  an intertwiner modulo the range of `q₀`.

The Frobenius map `D : K(src) → K(ind)` with the tail multiplier is an intertwiner with
`D ∘ q₁ = id`, and its kernel lies in the range of `q₀`. Hence the defects of `q₁` lie in the
range of `q₀`, and every `g` is `(g - q₁ (D g)) + q₁ (D g)` with `g - q₁ (D g) ∈ ker D`.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealCharacterPairReducible

open RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier RealCharacterPair
open RealBlockJacquet
open Langlands.LocalFactor.Archimedean

/-! ## General facts about Frobenius maps -/

section General

variable {n : ℕ}

/-- Intertwiners modulo a subspace are intertwiners modulo every larger subspace. -/
theorem IsRealIntertwinerModulo.mono {ds es : List RealBlock}
    {M N : Submodule ℂ (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n))}
    {q : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    (h : IsRealIntertwinerModulo n ds es M q) (hMN : M ≤ N) :
    IsRealIntertwinerModulo n ds es N q := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, hg, hm⟩ := h.1 k f
    exact ⟨hf, hg, hMN hm⟩
  · obtain ⟨hf, hg, hm⟩ := h.2 X f
    exact ⟨hf, hg, hMN hm⟩

variable {ds es fs : List RealBlock} {p : ℕ} {ε : ℤ}

/-- A Frobenius map with an intertwining left inverse `D` along the same block is an
intertwiner modulo every subspace containing the kernel of `D`. -/
theorem isRealIntertwinerModulo_of_leftInverse {σ σ' : ℂ} {μ μ' : ℤ → ℂ}
    (h : IsBlockFrobData n ds es p ε σ μ) (h' : IsBlockFrobData n es ds p ε σ' μ')
    (hrec' : IsRecurrent (GramFormula.realPositionExponent es p - GramFormula.realPositionExponent es (p + 1) + 1) ε μ')
    (hinv : ∀ f, blockFrobMap h' (blockFrobMap h f) = f)
    (M : Submodule ℂ (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)))
    (hM : LinearMap.ker (blockFrobMap h') ≤ M) :
    IsRealIntertwinerModulo n ds es M (blockFrobMap h) := by
  refine ⟨fun k f => ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2,
      rightTranslation_mem_kFiniteFunctions_realStandardModule n es (blockFrobMap h f).2 k.2,
      ?_⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X,
      rightDerivative_mem_kFiniteFunctions_realStandardModule n es (blockFrobMap h f).2 X, ?_⟩⟩
  · rw [blockFrobMap_mk_rightTranslation h k f _
      (rightTranslation_mem_kFiniteFunctions_realStandardModule n es (blockFrobMap h f).2 k.2),
      sub_self]
    exact M.zero_mem
  · apply hM
    rw [LinearMap.mem_ker, map_sub, hinv,
      blockFrobMap_mk_rightDerivative h' hrec' X (blockFrobMap h f) _
        (rightDerivative_mem_kFiniteFunctions_realStandardModule n ds
          (blockFrobMap h' (blockFrobMap h f)).2 X),
      sub_eq_zero]
    apply Subtype.ext
    show rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) X
        (blockFrobMap h' (blockFrobMap h f) : Langlands.GeneralLinear n ℝ → ℂ)
    rw [hinv]

/-- The block Fourier coefficients of the zero function vanish. -/
theorem blockFourierCoefficient_zero (j : ℤ) (g : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n p j (0 : Langlands.GeneralLinear n ℝ → ℂ) g = 0 := by
  simp [blockFourierCoefficient]

/-- Let `q = blockFrobMap h₀` (multiplier `μ`), `B = blockFrobMap h_B` in the opposite
direction (multiplier `μ'`) and `D = blockFrobMap h_D` (multiplier `P`) along the same block.
If `P_j ≠ 0` whenever `μ_j μ'_j ≠ 1` on the parity class, the kernel of `D` lies in the range
of `q`: for `D g = 0`, `q (B g) = g`. -/
theorem ker_le_range {σ σ' τ : ℂ} {μ μ' P : ℤ → ℂ}
    (h₀ : IsBlockFrobData n ds es p ε σ μ) (hB : IsBlockFrobData n es ds p ε σ' μ')
    (hD : IsBlockFrobData n es fs p ε τ P)
    (hsupp : ∀ j : ℤ, Even (j - ε) → μ j * μ' j ≠ 1 → P j ≠ 0) :
    LinearMap.ker (blockFrobMap hD) ≤ LinearMap.range (blockFrobMap h₀) := by
  intro g hg
  rw [LinearMap.mem_ker] at hg
  refine ⟨blockFrobMap hB g, blockFrobMap_blockFrobMap_eq hB h₀ g fun j hj hne k hk => ?_⟩
  have e := blockFourierCoefficient_blockFrobMap hD g hk j
  rw [hg, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_left (hsupp j hj hne)

end General

/-! ## Signs -/

section Signs

theorem inv_eq_self_of_sq_eq_one {x : ℂ} (h : x ^ 2 = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, h])

theorem neg_one_pow_sq_fin (e : Fin 2) : ((-1 : ℂ) ^ e.val) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem neg_one_pow_natAbs {ε : ℤ} (hε : ε = 0 ∨ ε = 1) : (-1 : ℂ) ^ ε.natAbs = (-1) ^ ε := by
  rcases hε with rfl | rfl <;> simp

theorem neg_one_pow_succ_mod_two {ℓ : ℕ} {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) : (-1 : ℂ) ^ ((ℓ + 1) % 2) = (-1) ^ ε := by
  obtain ⟨r, hr⟩ := hpar
  rcases hε with rfl | rfl
  · have : (ℓ + 1) % 2 = 0 := by omega
    simp [this]
  · have : (ℓ + 1) % 2 = 1 := by omega
    simp [this]

/-- `(-1)^ε = (-1)^{e_c} (-1)^{e_d}` for `ε = pairParity c d`. -/
theorem neg_one_pow_pairParity' (c d : RealCharacterData) :
    (-1 : ℂ) ^ pairParity c d = (-1) ^ c.parity.val * (-1) ^ d.parity.val := by
  rw [neg_one_pow_pairParity, character_neg_one, character_neg_one]

end Signs

/-! ## Positions of `pre ++ ws ++ post` -/

section Mid

variable (pre post : List RealBlock)

theorem exponent_mid_zero {ws : List RealBlock} (h : 0 < realRank ws) :
    GramFormula.realPositionExponent (pre ++ ws ++ post) (realRank pre) = GramFormula.realPositionExponent ws 0 := by
  have e := realPositionExponent_mid pre ws post h
  rwa [add_zero] at e

theorem exponent_mid_one {ws : List RealBlock} (h : 1 < realRank ws) :
    GramFormula.realPositionExponent (pre ++ ws ++ post) (realRank pre + 1) = GramFormula.realPositionExponent ws 1 :=
  realPositionExponent_mid pre ws post h

theorem realRank_mid_eq {ws ws' : List RealBlock} (h : realRank ws = realRank ws') :
    realRank (pre ++ ws ++ post) = realRank (pre ++ ws' ++ post) := by
  simp only [realRank] at h ⊢
  simp [List.map_append, List.sum_append, h]

theorem mid_pair (x y : RealBlock) : pre ++ [x, y] ++ post = pre ++ x :: y :: post := by
  simp

end Mid

/-! ## The four Frobenius maps -/

section Maps

variable {n : ℕ} {pre post : List RealBlock} {c d : RealCharacterData} {ℓ : ℕ}

/-- The list `[c, d]` of two character blocks. -/
abbrev cd (c d : RealCharacterData) : List RealBlock :=
  [RealBlock.character c, RealBlock.character d]

/-- The list `[d, c]`. -/
abbrev dc (c d : RealCharacterData) : List RealBlock :=
  [RealBlock.character d, RealBlock.character c]

/-- The list consisting of the real induction of `pairInduced c d ℓ`. -/
abbrev indBlock (c d : RealCharacterData) (ℓ : ℕ) : List RealBlock :=
  [RealBlock.induced (pairInduced c d ℓ)]

theorem realRank_cd : realRank (cd c d) = 2 := rfl
theorem realRank_dc : realRank (dc c d) = 2 := rfl
theorem realRank_indBlock : realRank (indBlock c d ℓ) = 2 := rfl

theorem realRank_dc_mid (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n) :
    realRank (pre ++ dc c d ++ post) = n := by
  rw [← hn, ← mid_pair pre post (RealBlock.character c) (RealBlock.character d)]
  exact realRank_mid_eq pre post rfl

theorem realRank_cd_mid (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n) :
    realRank (pre ++ cd c d ++ post) = n := by
  rw [← hn, ← mid_pair pre post (RealBlock.character c) (RealBlock.character d)]

theorem realRank_ind_mid (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n) :
    realRank (pre ++ indBlock c d ℓ ++ post) = n := by
  rw [← hn, ← mid_pair pre post (RealBlock.character c) (RealBlock.character d)]
  exact realRank_mid_eq pre post rfl

/-- The sign `σ₀ = (-1)^ε` of the binomial multiplier. -/
def sigma0 (c d : RealCharacterData) : ℂ := (-1) ^ (pairParity c d).natAbs

theorem sigma0_eq (c d : RealCharacterData) :
    sigma0 c d = (-1) ^ c.parity.val * (-1) ^ d.parity.val := by
  rw [sigma0, neg_one_pow_natAbs (pairParity_eq c d), neg_one_pow_pairParity']

theorem sigma0_inv (c d : RealCharacterData) : (sigma0 c d)⁻¹ = sigma0 c d := by
  apply inv_eq_self_of_sq_eq_one
  rw [sigma0_eq, mul_pow, neg_one_pow_sq_fin, neg_one_pow_sq_fin, one_mul]

/-- The Frobenius data from `swp` to `src` for any multiplier with the symmetry sign `σ₀`. -/
theorem data_swap {μ : ℤ → ℂ}
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hsym : IsSymmetric (pairParity c d) (sigma0 c d) μ) :
    IsBlockFrobData n (pre ++ dc c d ++ post)
      (pre ++ RealBlock.character c :: RealBlock.character d :: post) (realRank pre)
      (pairParity c d) (sigma0 c d) μ := by
  rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character d)]
  refine IsBlockFrobData.of_mid (realRank_cd_mid hn) rfl rfl rfl rfl ?_ hsym ?_ ?_ ?_
  · simp only [realPositionCharacter_neg_one, neg_one_pow_pairParity']
    simp only [realPositionSign]
    ring
  · simp only [realPositionCharacter_neg_one, sigma0_eq]
    simp only [realPositionSign]
    linear_combination -(-1 : ℂ) ^ c.parity.val * neg_one_pow_sq_fin d.parity
  · simp only [realPositionCharacter_neg_one, sigma0_eq]
    simp only [realPositionSign]
    linear_combination -(-1 : ℂ) ^ d.parity.val * neg_one_pow_sq_fin c.parity
  · intro e he
    simp [realInducedBlockAt] at he

/-- The Frobenius data from `src` to `swp` for the pointwise inverse of a multiplier with the
symmetry sign `σ₀`. -/
theorem data_unswap {μ : ℤ → ℂ}
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hsym : IsSymmetric (pairParity c d) (sigma0 c d) μ) :
    IsBlockFrobData n (pre ++ RealBlock.character c :: RealBlock.character d :: post)
      (pre ++ dc c d ++ post) (realRank pre)
      (pairParity c d) (sigma0 c d)⁻¹ (fun k => (μ k)⁻¹) := by
  rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character d)]
  refine IsBlockFrobData.of_mid (realRank_dc_mid hn) rfl rfl rfl rfl ?_ hsym.inv ?_ ?_ ?_
  · simp only [realPositionCharacter_neg_one, neg_one_pow_pairParity']
    simp only [realPositionSign]
  · rw [sigma0_inv, sigma0_eq]
    simp only [realPositionCharacter_neg_one]
    simp only [realPositionSign]
    linear_combination -(-1 : ℂ) ^ d.parity.val * neg_one_pow_sq_fin c.parity
  · rw [sigma0_inv, sigma0_eq]
    simp only [realPositionCharacter_neg_one]
    simp only [realPositionSign]
    linear_combination -(-1 : ℂ) ^ c.parity.val * neg_one_pow_sq_fin d.parity
  · intro e he
    simp [realInducedBlockAt] at he

/-- `q₀`: the binomial multiplier from `swp` to `src`. -/
theorem data_q0 (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n) :
    IsBlockFrobData n (pre ++ dc c d ++ post)
      (pre ++ RealBlock.character c :: RealBlock.character d :: post) (realRank pre)
      (pairParity c d) (sigma0 c d) (binomialMultiplier ℓ (pairParity c d)) :=
  data_swap hn (isSymmetric_binomialMultiplier ℓ (pairParity_eq c d))

/-- The inverse of the binomial multiplier from `src` to `swp`. -/
theorem data_B (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n) :
    IsBlockFrobData n (pre ++ RealBlock.character c :: RealBlock.character d :: post)
      (pre ++ dc c d ++ post) (realRank pre)
      (pairParity c d) (sigma0 c d)⁻¹ (fun k => (binomialMultiplier ℓ (pairParity c d) k)⁻¹) :=
  data_unswap hn (isSymmetric_binomialMultiplier ℓ (pairParity_eq c d))

/-- The exponent of `swp` at the first position of the block is `t_d`. -/
theorem exponent_swp_zero :
    GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre) = d.exponent := by
  rw [exponent_mid_zero pre post (realRank_dc (c := c) (d := d) ▸ two_pos)]
  rfl

/-- The exponent of `swp` at the second position of the block is `t_c`. -/
theorem exponent_swp_one :
    GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre + 1) = c.exponent := by
  rw [exponent_mid_one pre post (realRank_dc (c := c) (d := d) ▸ one_lt_two)]
  rfl

theorem exponent_indBlock_zero (hν : d.exponent - c.exponent = ℓ) :
    GramFormula.realPositionExponent (indBlock c d ℓ) 0 = d.exponent := by
  simp only [GramFormula.realPositionExponent, pairInduced_weight, pairInduced_exponent, Int.natAbs_natCast]
  linear_combination -hν / 2

theorem exponent_indBlock_one (hν : d.exponent - c.exponent = ℓ) :
    GramFormula.realPositionExponent (indBlock c d ℓ) 1 = c.exponent := by
  simp only [GramFormula.realPositionExponent, pairInduced_weight, pairInduced_exponent, Int.natAbs_natCast]
  linear_combination hν / 2

theorem sign_indBlock_zero (c d : RealCharacterData) (ℓ : ℕ) :
    ((realPositionSign (indBlock c d ℓ) 0).val : ℕ) = (ℓ + 1) % 2 := by
  simp [realPositionSign]

theorem sign_indBlock_one (c d : RealCharacterData) (ℓ : ℕ) :
    realPositionSign (indBlock c d ℓ) 1 = 0 := rfl

/-- `D`: the tail multiplier from `src` to `ind`. -/
theorem data_D (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (hν : d.exponent - c.exponent = ℓ) :
    IsBlockFrobData n (pre ++ RealBlock.character c :: RealBlock.character d :: post)
      (pre ++ indBlock c d ℓ ++ post) (realRank pre)
      (pairParity c d) ((-1) ^ d.parity.val)
      (tailMultiplier ℓ (pairParity c d) ((-1) ^ d.parity.val)) := by
  rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character d)]
  refine IsBlockFrobData.of_mid (realRank_ind_mid hn) rfl rfl ?_ ?_ ?_
    (isSymmetric_tailMultiplier hℓ (pairParity_eq c d) hpar (neg_one_pow_sq_fin d.parity))
    ?_ ?_ ?_
  · rw [exponent_indBlock_zero hν]
    rfl
  · rw [exponent_indBlock_one hν]
    rfl
  · simp only [realPositionCharacter_neg_one, neg_one_pow_pairParity']
    simp only [realPositionSign]
  · rw [sign_indBlock_zero, neg_one_pow_succ_mod_two (pairParity_eq c d) hpar,
      neg_one_pow_pairParity', realPositionCharacter_neg_one]
    simp only [realPositionSign]
  · rw [sign_indBlock_one, realPositionCharacter_neg_one]
    simp only [realPositionSign, Fin.val_zero, pow_zero]
    rw [← sq, neg_one_pow_sq_fin]
  · intro e he j hj hjl
    simp only [realInducedBlockAt, Option.some.injEq] at he
    subst he
    by_contra hne
    have := (tailMultiplier_ne_zero_iff hℓ (pairParity_eq c d) hpar
      (neg_one_pow_sq_fin d.parity) hj).mp hne
    rw [pairInduced_weight, abs_of_nonneg (Int.natCast_nonneg ℓ)] at hjl
    omega

/-- `q₁`: the inverse of the tail multiplier from `ind` to `src`. -/
theorem data_q1 (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (hν : d.exponent - c.exponent = ℓ) :
    IsBlockFrobData n (pre ++ indBlock c d ℓ ++ post)
      (pre ++ RealBlock.character c :: RealBlock.character d :: post) (realRank pre)
      (pairParity c d) ((-1) ^ d.parity.val)⁻¹
      (fun k => (tailMultiplier ℓ (pairParity c d) ((-1) ^ d.parity.val) k)⁻¹) := by
  rw [← mid_pair pre post (RealBlock.character c) (RealBlock.character d)]
  have hs : ((-1 : ℂ) ^ d.parity.val)⁻¹ = (-1) ^ d.parity.val :=
    inv_eq_self_of_sq_eq_one (neg_one_pow_sq_fin d.parity)
  refine IsBlockFrobData.of_mid (realRank_cd_mid hn) rfl rfl ?_ ?_ ?_
    (isSymmetric_tailMultiplier hℓ (pairParity_eq c d) hpar (neg_one_pow_sq_fin d.parity)).inv
    ?_ ?_ ?_
  · rw [exponent_indBlock_one hν]
    rfl
  · rw [exponent_indBlock_zero hν]
    rfl
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one, sign_indBlock_zero,
      sign_indBlock_one, neg_one_pow_succ_mod_two (pairParity_eq c d) hpar]
    simp
  · rw [hs, realPositionCharacter_neg_one, sign_indBlock_zero,
      neg_one_pow_succ_mod_two (pairParity_eq c d) hpar, neg_one_pow_pairParity']
    simp only [realPositionSign]
    linear_combination -(-1 : ℂ) ^ c.parity.val * neg_one_pow_sq_fin d.parity
  · rw [hs, realPositionCharacter_neg_one, sign_indBlock_one]
    simp only [realPositionSign, Fin.val_zero, pow_zero, one_mul]
  · intro e he
    simp [realInducedBlockAt] at he

end Maps

/-! ## The filtration -/

section Filtration

variable {n : ℕ} {pre post : List RealBlock} {c d : RealCharacterData} {ℓ : ℕ}

theorem abs_lt_of_parity {ℓ : ℕ} {ε j : ℤ} (hpar : Even ((ℓ : ℤ) - 1 - ε)) (hj : Even (j - ε))
    (h : |j| ≤ ℓ) : |j| < ℓ := by
  obtain ⟨r, hr⟩ := hpar
  obtain ⟨s, hs⟩ := hj
  rcases abs_cases j with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] at h ⊢ <;> omega

/-- **The reducible case.** If `t_d - t_c = ℓ` is a positive integer with
`ℓ - 1 ≡ pairParity c d (mod 2)`, the standard module of `pre ++ c :: d :: post` has the
two-step filtration with pieces `[d, c]` and `[induced (pairInduced c d ℓ)]`. -/
theorem realAdjacentFiltration_of_reducible
    (hn : realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n)
    (hℓ : 0 < ℓ) (hpar : Even ((ℓ : ℤ) - 1 - pairParity c d))
    (hν : d.exponent - c.exponent = ℓ) :
    RealAdjacentFiltration n pre post (RealBlock.character c) (RealBlock.character d) := by
  set ε := pairParity c d with hεdef
  have hε : ε = 0 ∨ ε = 1 := pairParity_eq c d
  have hσd := neg_one_pow_sq_fin d.parity
  have h0 := data_q0 (ℓ := ℓ) hn
  have hB := data_B (ℓ := ℓ) hn
  have hD := data_D hn hℓ hpar hν
  have h1 := data_q1 hn hℓ hpar hν
  -- the exponents of `src` and `swp` on the block
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
  have e_swp0 := exponent_swp_zero (pre := pre) (post := post) (c := c) (d := d)
  have e_swp1 := exponent_swp_one (pre := pre) (post := post) (c := c) (d := d)
  have hrec0 : IsRecurrent (GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre) -
      GramFormula.realPositionExponent (pre ++ dc c d ++ post) (realRank pre + 1) + 1) ε
      (binomialMultiplier ℓ ε) := by
    rw [e_swp0, e_swp1, hν]
    exact isRecurrent_binomialMultiplier hℓ hε hpar
  have hrecD : IsRecurrent
      (GramFormula.realPositionExponent (pre ++ RealBlock.character c :: RealBlock.character d :: post)
        (realRank pre) -
      GramFormula.realPositionExponent (pre ++ RealBlock.character c :: RealBlock.character d :: post)
        (realRank pre + 1) + 1) ε (tailMultiplier ℓ ε ((-1) ^ d.parity.val)) := by
    rw [e_src0, e_src1, show c.exponent - d.exponent + 1 = 1 - (ℓ : ℂ) by
      linear_combination -hν]
    exact isRecurrent_tailMultiplier hℓ hε hpar hσd
  -- `D ∘ q₁ = id`
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
  -- `ker D ≤ range q₀`
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
  -- the two pieces
  let ws : Fin 2 → List RealBlock := ![dc c d, indBlock c d ℓ]
  let q : ∀ j : Fin 2,
      kFiniteFunctions (realStandardModule n (pre ++ ws j ++ post)) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n
          (pre ++ RealBlock.character c :: RealBlock.character d :: post)) (unitaryCompact ℝ n) :=
    Fin.cons (α := fun j : Fin 2 =>
      kFiniteFunctions (realStandardModule n (pre ++ ws j ++ post)) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n
          (pre ++ RealBlock.character c :: RealBlock.character d :: post)) (unitaryCompact ℝ n))
      (blockFrobMap h0) (Fin.cons (blockFrobMap h1) finZeroElim)
  refine ⟨2, ws, q, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, ?_⟩
      · exact realExponentSupport_pairInduced hν
      · exact realWeightSquareSum_lt_pairInduced c d hℓ
  · intro j
    fin_cases j
    · exact isRealIntertwinerModulo_blockFrobMap h0 hrec0 _
    · refine isRealIntertwinerModulo_of_leftInverse h1 hD hrecD hinv _ (hker.trans ?_)
      exact le_iSup₂_of_le (f := fun (i : Fin 2) (_ : i < 1) => LinearMap.range (q i))
        (0 : Fin 2) (by decide) le_rfl
  · refine eq_top_iff.2 fun g _ => ?_
    have hg : g - blockFrobMap h1 (blockFrobMap hD g) ∈ LinearMap.ker (blockFrobMap hD) := by
      rw [LinearMap.mem_ker, map_sub, hinv, sub_self]
    obtain ⟨a, ha⟩ := hker hg
    have m0 : blockFrobMap h0 a ∈ ⨆ j, LinearMap.range (q j) :=
      Submodule.mem_iSup_of_mem (0 : Fin 2) ⟨a, rfl⟩
    have m1 : blockFrobMap h1 (blockFrobMap hD g) ∈ ⨆ j, LinearMap.range (q j) :=
      Submodule.mem_iSup_of_mem (1 : Fin 2) ⟨blockFrobMap hD g, rfl⟩
    rw [← sub_add_cancel g (blockFrobMap h1 (blockFrobMap hD g)), ← ha]
    exact add_mem m0 m1

/-- The filtration statement for two characters follows from its generic case
(`t_d - t_c ≠ pairParity c d + 2m + 1` for every `m`), because the remaining case is the
reducible one (`generic_or_reducible`). -/
theorem realCharacterPairFiltration_of_generic
    (hgen : ∀ (n : ℕ) (pre post : List RealBlock) (c d : RealCharacterData),
      realRank (pre ++ RealBlock.character c :: RealBlock.character d :: post) = n →
      realBlockExponent (RealBlock.character c) < realBlockExponent (RealBlock.character d) →
      (∀ m : ℕ, d.exponent - c.exponent ≠ (pairParity c d : ℂ) + 2 * m + 1) →
      RealAdjacentFiltration n pre post (RealBlock.character c) (RealBlock.character d)) :
    RealCharacterPairFiltrationStatement := by
  intro n pre post c d hn hlt
  rcases generic_or_reducible c d with hne | ⟨ℓ, hℓ, hpar, hν⟩
  · exact hgen n pre post c d hn hlt hne
  · exact realAdjacentFiltration_of_reducible hn hℓ hpar hν

end Filtration

end RealCharacterPairReducible

end Langlands.Archimedean
