import Langlands.LocalFactor.ArchimedeanPairFactor
import Langlands.Representation.Archimedean.RealCharacterPairReducible
import Langlands.Representation.Archimedean.RealBlockMultiplierGeneric
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-!
# Splitting the induction blocks of a real standard module

For a list `ds` of real blocks, `split ds` replaces every induction block of weight `m` and
exponent `t` by the two character blocks `|·|^(t - |m|/2)` and `sgn^(|m|+1) |·|^(t + |m|/2)`,
in this order. This module builds a surjective intertwiner `D` from the `O(n)`-finite functions
of the standard module of `split ds` onto those of `ds` (`exists_splitMap`), as a composite of
the Frobenius maps of module `RealBlockFrobeniusMap` along the induction blocks, with a
right inverse `Q` that commutes with `O(n)`. Its kernel is orthogonal, for the `O(n)`-pairing,
to every `O(n)`-finite function whose block Fourier coefficients of weight `|j| < |m|` vanish
on `O(n)` along every induction block.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

open MeasureTheory

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealSplitFrobenius

open RealJacquetFrobenius RealBlockFrobeniusMap RealBlockPosition RealBlockMultiplier
open RealBlockJacquet RealBlockFourierFinite RealCharacterPairReducible RealPrincipalSeriesDuality
open RealBlockRotation
open Langlands.LocalFactor.Archimedean

attribute [local instance] measurableSpaceK

local instance borelSpaceK_sf (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-! ## The split list -/

/-- The parity class `(ℓ + 1) mod 2` of the modes of a split induction block of weight `ℓ`. -/
def splitParity (ℓ : ℕ) : ℤ := (((ℓ + 1) % 2 : ℕ) : ℤ)

/-- The sign `(-1)^((ℓ + 1) mod 2)`. -/
def splitSign (ℓ : ℕ) : ℂ := (-1) ^ ((ℓ + 1) % 2)

/-- The lower character `|·|^(t - |m|/2)` of an induction block. -/
def lowChar (e : ComplexCharacterData) : RealCharacterData :=
  charData 0 (e.exponent - (e.weight.natAbs : ℂ) / 2)

/-- The upper character `sgn^(|m|+1) |·|^(t + |m|/2)` of an induction block. -/
def highChar (e : ComplexCharacterData) : RealCharacterData :=
  charData ⟨(e.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩
    (e.exponent + (e.weight.natAbs : ℂ) / 2)

/-- A character block stays; an induction block becomes its lower and upper characters. -/
def splitBlock : RealBlock → List RealBlock
  | .character c => [.character c]
  | .induced e => [.character (lowChar e), .character (highChar e)]

/-- Split every induction block. -/
def split : List RealBlock → List RealBlock
  | [] => []
  | b :: ds => splitBlock b ++ split ds

theorem realRank_append' (xs ys : List RealBlock) :
    realRank (xs ++ ys) = realRank xs + realRank ys :=
  Langlands.LocalFactor.Archimedean.realRank_append xs ys

theorem realRank_splitBlock (b : RealBlock) : realRank (splitBlock b) = realRank [b] := by
  cases b <;> rfl

theorem realRank_split : ∀ ds : List RealBlock, realRank (split ds) = realRank ds
  | [] => rfl
  | b :: ds => by
    rw [split, realRank_append', realRank_splitBlock, realRank_split ds, ← realRank_append']
    rfl

theorem splitParity_eq (ℓ : ℕ) : splitParity ℓ = 0 ∨ splitParity ℓ = 1 := by
  unfold splitParity
  omega

theorem even_splitParity (ℓ : ℕ) : Even ((ℓ : ℤ) - 1 - splitParity ℓ) := by
  unfold splitParity
  rw [Int.even_iff]
  omega

theorem splitSign_sq (ℓ : ℕ) : splitSign ℓ ^ 2 = 1 := by
  unfold splitSign
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem neg_one_zpow_splitParity (ℓ : ℕ) : (-1 : ℂ) ^ splitParity ℓ = splitSign ℓ := by
  unfold splitParity splitSign
  rw [zpow_natCast]

/-! ## Multipliers -/

/-- A symmetric solution of the recurrence for `δ = 1 - ℓ` on the parity class of a split
induction block of weight `ℓ` that vanishes exactly on the window `|j| < ℓ`: the tail
multiplier for `ℓ > 0` and the generic multiplier for `ℓ = 0`. -/
theorem exists_unsplitMultiplier (ℓ : ℕ) :
    ∃ μ : ℤ → ℂ, IsSymmetric (splitParity ℓ) (splitSign ℓ) μ ∧
      IsRecurrent (1 - (ℓ : ℂ)) (splitParity ℓ) μ ∧
      ∀ j : ℤ, Even (j - splitParity ℓ) → (μ j = 0 ↔ |j| < ℓ) := by
  have hε := splitParity_eq ℓ
  have hσ := splitSign_sq ℓ
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have hε1 : splitParity 0 = 1 := rfl
    have hne : ∀ m : ℕ, (0 : ℂ) ≠ ((splitParity 0 : ℤ) : ℂ) + 2 * m + 1 := by
      intro m h
      have := congrArg Complex.re h
      simp [hε1] at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hden : ∀ m : ℕ, (0 : ℂ) ≠ -(((splitParity 0 : ℤ) : ℂ) + 2 * m + 1) := by
      intro m h
      have := congrArg Complex.re h
      simp [hε1] at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    refine ⟨genericMultiplier 0 (splitParity 0), ?_, ?_, ?_⟩
    · have h := isSymmetric_genericMultiplier 0 hε
      rw [hε1] at h ⊢
      simpa [splitSign] using h
    · have h := isRecurrent_genericMultiplier_of_ne hε hden
      simpa using h
    · intro j _
      simp only [CharP.cast_eq_zero]
      refine iff_of_false (genericMultiplier_ne_zero_of_ne hne hden j) ?_
      exact not_lt.mpr (abs_nonneg j)
  · have hpar := even_splitParity ℓ
    refine ⟨tailMultiplier ℓ (splitParity ℓ) (splitSign ℓ),
      isSymmetric_tailMultiplier hℓ hε hpar hσ, isRecurrent_tailMultiplier hℓ hε hpar hσ,
      fun j hj => ?_⟩
    rw [← not_iff_not, ← Ne, tailMultiplier_ne_zero_iff hℓ hε hpar hσ hj, not_lt]
    constructor
    · exact le_of_lt
    · intro h
      rcases h.lt_or_eq with h | h
      · exact h
      · exact absurd (abs_lt_of_parity hpar hj h.symm.le) (by omega)

/-! ## The Frobenius data along one induction block -/

variable {n : ℕ}

section Data

variable {pre post : List RealBlock} (e : ComplexCharacterData)

theorem realRank_splitBlock_mid :
    realRank (pre ++ splitBlock (.induced e) ++ post) =
      realRank (pre ++ [RealBlock.induced e] ++ post) := by
  simp only [realRank_append', realRank_splitBlock]

/-- `D`: from the split block to the induction block, multiplier `μ`. -/
theorem data_unsplit {μ : ℤ → ℂ} (hn : realRank (pre ++ [RealBlock.induced e] ++ post) = n)
    (hsym : IsSymmetric (splitParity e.weight.natAbs) (splitSign e.weight.natAbs) μ)
    (hzero : ∀ j : ℤ, Even (j - splitParity e.weight.natAbs) →
      (μ j = 0 ↔ |j| < e.weight.natAbs)) :
    IsBlockFrobData n (pre ++ splitBlock (.induced e) ++ post)
      (pre ++ [RealBlock.induced e] ++ post) (realRank pre) (splitParity e.weight.natAbs)
      (splitSign e.weight.natAbs) μ := by
  refine IsBlockFrobData.of_mid hn rfl rfl ?_ ?_ ?_ hsym ?_ ?_ ?_
  · simp [GramFormula.realPositionExponent, splitBlock, highChar, charData]
  · simp [GramFormula.realPositionExponent, splitBlock, lowChar, charData]
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one,
      neg_one_zpow_splitParity]
    simp [realPositionSign, splitBlock, lowChar, highChar, charData, splitSign]
  · simp [realPositionSign, realPositionCharacter_neg_one, splitBlock, lowChar, charData,
      splitSign]
  · rw [realPositionCharacter_neg_one]
    simp only [realPositionSign, splitBlock, highChar, charData, Fin.val_zero, pow_zero]
    show (1 : ℂ) = splitSign _ * splitSign _
    rw [← sq, splitSign_sq]
  · intro d hd j hj hjl
    simp only [realInducedBlockAt, Option.some.injEq] at hd
    subst hd
    refine (hzero j hj).mpr ?_
    rwa [Int.abs_eq_natAbs e.weight] at hjl

/-- `Q`: from the induction block back to the split block, multiplier `μ⁻¹`. -/
theorem data_resplit {μ : ℤ → ℂ} (hn : realRank (pre ++ [RealBlock.induced e] ++ post) = n)
    (hsym : IsSymmetric (splitParity e.weight.natAbs) (splitSign e.weight.natAbs) μ) :
    IsBlockFrobData n (pre ++ [RealBlock.induced e] ++ post)
      (pre ++ splitBlock (.induced e) ++ post) (realRank pre) (splitParity e.weight.natAbs)
      (splitSign e.weight.natAbs)⁻¹ (fun k => (μ k)⁻¹) := by
  have hs : (splitSign e.weight.natAbs)⁻¹ = splitSign e.weight.natAbs :=
    inv_eq_self_of_sq_eq_one (splitSign_sq _)
  refine IsBlockFrobData.of_mid ((realRank_splitBlock_mid e).trans hn) rfl rfl ?_ ?_ ?_
    hsym.inv ?_ ?_ ?_
  · simp [GramFormula.realPositionExponent, splitBlock, lowChar, charData]
  · simp [GramFormula.realPositionExponent, splitBlock, highChar, charData]
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one,
      neg_one_zpow_splitParity]
    simp [realPositionSign, splitSign]
  · rw [hs, realPositionCharacter_neg_one]
    simp only [realPositionSign, splitBlock, lowChar, charData, Fin.val_zero, pow_zero]
    rw [splitSign, ← sq, ← pow_mul, mul_comm, pow_mul]
    norm_num
  · rw [hs, realPositionCharacter_neg_one]
    simp [realPositionSign, splitBlock, highChar, charData, splitSign]
  · intro d hd
    simp [realInducedBlockAt, splitBlock] at hd

end Data

/-! ## Intertwiners that commute with the actions -/

section Commutes

variable (n) {xs ys zs : List RealBlock}

/-- `D` commutes with the actions of `O(n)` and of the real Lie algebra on the
`O(n)`-finite functions of the standard modules of `xs` and `ys`. -/
def Commutes (D : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n) →ₗ[ℂ]
    kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n)) : Prop :=
  (∀ (k : Matrix.unitaryGroup (Fin n) ℝ)
      (f : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n)),
    D (realStandardRep n xs k f) = realStandardRep n ys k (D f)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) ℝ)
      (f : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n)),
    D (realStandardLie n xs (1 ⊗ₜ X) f) = realStandardLie n ys (1 ⊗ₜ X) (D f)

variable {n}

theorem commutes_id : Commutes n (LinearMap.id :
    kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n)) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem Commutes.comp
    {D : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n)}
    {E : kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n zs) (unitaryCompact ℝ n)}
    (hE : Commutes n E) (hD : Commutes n D) : Commutes n (E ∘ₗ D) :=
  ⟨fun k f => by simp only [LinearMap.comp_apply, hD.1, hE.1],
    fun X f => by simp only [LinearMap.comp_apply, hD.2, hE.2]⟩

theorem commutes_blockFrobMap {p : ℕ} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}
    (h : IsBlockFrobData n xs ys p ε σ μ)
    (hrec : IsRecurrent (GramFormula.realPositionExponent xs p - GramFormula.realPositionExponent xs (p + 1) + 1) ε μ) :
    Commutes n (blockFrobMap h) :=
  ⟨fun k f => blockFrobMap_rightTranslation h k f,
    fun X f => blockFrobMap_rightDerivative h hrec X f⟩

/-- A map that commutes with the actions is an intertwiner into the standard module of `ys`. -/
theorem Commutes.isRealStandardIntertwiner
    {D : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n)}
    (hD : Commutes n D) :
    IsRealStandardIntertwiner n (realStandardRep n ys) (realStandardLie n ys) xs D :=
  ⟨fun k f => ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n xs f.2 k.2, by
      rw [mk_rightTranslation_eq xs k f, hD.1]⟩,
    fun X f => ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n xs f.2 X, by
      rw [mk_rightDerivative_eq xs X f, hD.2]⟩⟩

end Commutes

/-! ## Fourier modes on `O(n)` -/

/-- A Fourier coefficient of a function vanishing on `O(N)` vanishes on `O(N)`. -/
theorem blockFourierCoefficient_eq_zero_of_eqOn {N p : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : ∀ g ∈ unitaryCompact ℝ N, F g = 0) (j : ℤ) {k : Langlands.GeneralLinear N ℝ}
    (hk : k ∈ unitaryCompact ℝ N) : blockFourierCoefficient N p j F k = 0 := by
  unfold blockFourierCoefficient
  have h : ∀ θ : ℝ, F (blockRotation N p θ * k) *
      Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) = 0 := fun θ => by
    rw [hF _ ((unitaryCompact ℝ N).mul_mem (blockRotation_mem_unitaryCompact N p θ) hk),
      zero_mul]
  simp only [h, intervalIntegral.integral_zero]

/-- **Disjoint blocks.** A Frobenius map along the block `p` keeps the vanishing on `O(n)` of
the Fourier coefficient along a disjoint block `p'`. -/
theorem blockFourierCoefficient_blockFrobMap_eq_zero {ds es : List RealBlock} {p : ℕ} {ε : ℤ}
    {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData n ds es p ε σ μ) {p' : ℕ}
    (hd : p + 1 < p' ∨ p' + 1 < p)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) (i : ℤ)
    (h0 : ∀ g ∈ unitaryCompact ℝ n, blockFourierCoefficient n p' i f g = 0)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    blockFourierCoefficient n p' i
      ((blockFrobMap h f : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ) k = 0 := by
  rw [blockFrobMap_apply_coe]
  obtain ⟨D, hD⟩ := exists_bound_coe p f
  set I : Finset ℤ := Finset.Icc (-(D : ℤ)) D with hI
  have horb : (fun φ : ℝ => RealJacquetFrobenius.frobFun (realStandardRep n ds)
      (blockJacquet n ds p μ) (shiftedExponent n es) (positionSign n es) f
        (blockRotation n p' φ * k)) =
      fun φ => ∑ j ∈ I, (2 * (Real.pi : ℂ))⁻¹ * μ j *
        blockFourierCoefficient n p j f (blockRotation n p' φ * k) := by
    funext φ
    have hm := (unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p' φ) hk
    rw [frobFun_apply_of_mem h.hsign f hm, finsum_eq_sum_of_support_subset (s := I),
      Finset.mul_sum]
    · simp_rw [mul_assoc]
    · intro j hj
      by_contra hjI
      refine hj ?_
      have hj' : (D : ℤ) < |j| := by
        rw [hI, Finset.coe_Icc, Set.mem_Icc, ← abs_le] at hjI
        exact not_le.mp hjI
      simp [hD j hj' _ hm]
  rw [blockFourierCoefficient_eq_coeff, horb, coeff_finset_sum I
    (fun j φ => (2 * (Real.pi : ℂ))⁻¹ * μ j *
      blockFourierCoefficient n p j f (blockRotation n p' φ * k)) fun j _ =>
    continuous_const.mul ((continuous_blockFourierCoefficient p j (continuous_coe f)).comp
      ((continuous_blockRotation n p').mul continuous_const))]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_const_mul]
  have hc : coeff i (fun φ => blockFourierCoefficient n p j f (blockRotation n p' φ * k)) =
      blockFourierCoefficient n p' i (blockFourierCoefficient n p j f) k := rfl
  rw [hc, ← blockFourierCoefficient_comm hd (continuous_coe f),
    blockFourierCoefficient_eq_zero_of_eqOn h0 j hk, mul_zero]

/-- **Orthogonality of Fourier modes.** If for every `j` either the `j`-th Fourier coefficient
of `a` or the `-j`-th Fourier coefficient of `F` along the block `p` vanishes on `O(N)`, then
`∫_{O(N)} a F = 0`. -/
theorem integral_mul_eq_zero_of_modes {N p : ℕ} (hp : p + 1 < N)
    {a F : Langlands.GeneralLinear N ℝ → ℂ} (ha : Continuous a)
    (haK : a ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (hF : Continuous F)
    (hFK : F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N))
    (h : ∀ j : ℤ, (∀ k ∈ unitaryCompact ℝ N, blockFourierCoefficient N p j a k = 0) ∨
      (∀ k ∈ unitaryCompact ℝ N, blockFourierCoefficient N p (-j) F k = 0)) :
    ∫ κ : unitaryCompact ℝ N, a (κ : Langlands.GeneralLinear N ℝ) *
      F (κ : Langlands.GeneralLinear N ℝ) ∂haarK N = 0 := by
  obtain ⟨Da, -, hsa⟩ := exists_eq_sum_blockFourierCoefficient hp ha haK
  obtain ⟨DF, -, hsF⟩ := exists_eq_sum_blockFourierCoefficient hp hF hFK
  set Ia : Finset ℤ := Finset.Icc (-(Da : ℤ)) Da
  set IF : Finset ℤ := Finset.Icc (-(DF : ℤ)) DF
  set c : ℂ := (2 * (Real.pi : ℂ))⁻¹
  have hexp0 : ∀ j : ℤ, expMode j 0 = 1 := fun j => by simp [expMode]
  have e : ∀ κ : unitaryCompact ℝ N, a (κ : Langlands.GeneralLinear N ℝ) *
      F (κ : Langlands.GeneralLinear N ℝ) = ∑ j ∈ Ia, ∑ j' ∈ IF, c * c *
        (blockFourierCoefficient N p j a κ * blockFourierCoefficient N p j' F κ) := by
    intro κ
    have h1 := hsa κ κ.2 0
    have h2 := hsF κ κ.2 0
    rw [blockRotation_zero, one_mul] at h1 h2
    rw [h1, h2]
    simp only [hexp0, mul_one]
    rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hcont : ∀ (j : ℤ) (G : Langlands.GeneralLinear N ℝ → ℂ), Continuous G →
      Continuous (blockFourierCoefficient N p j G) :=
    fun j G hG => continuous_blockFourierCoefficient p j hG
  have hint : ∀ j j' : ℤ, Integrable (fun κ : unitaryCompact ℝ N =>
      c * c * (blockFourierCoefficient N p j a κ * blockFourierCoefficient N p j' F κ))
        (haarK N) := fun j j' =>
    (integrable_mul_of_continuous (hcont j a ha) (hcont j' F hF)).const_mul _
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => hint j j']
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finsetSum _ fun j' _ => hint j j']
  refine Finset.sum_eq_zero fun j' _ => ?_
  rw [integral_const_mul]
  suffices hI : ∫ κ : unitaryCompact ℝ N, blockFourierCoefficient N p j a κ *
      blockFourierCoefficient N p j' F κ ∂haarK N = 0 by rw [hI, mul_zero]
  by_cases hjj : j + j' = 0
  · have hj' : j' = -j := by omega
    subst hj'
    rcases h j with h0 | h0
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun κ => ?_)
      simp only [Pi.zero_apply]
      rw [h0 κ κ.2, zero_mul]
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun κ => ?_)
      simp only [Pi.zero_apply]
      rw [h0 κ κ.2, mul_zero]
  · set θ : ℝ := Real.pi / ((j + j' : ℤ) : ℝ) with hθ
    set r : unitaryCompact ℝ N := ⟨blockRotation N p θ, blockRotation_mem_unitaryCompact N p θ⟩
    set G : unitaryCompact ℝ N → ℂ := fun κ => blockFourierCoefficient N p j a κ *
      blockFourierCoefficient N p j' F κ with hG
    have hrot : ∀ κ : unitaryCompact ℝ N, G (r * κ) = -G κ := fun κ => by
      have hcoe : ((r * κ : unitaryCompact ℝ N) : Langlands.GeneralLinear N ℝ) =
          blockRotation N p θ * (κ : Langlands.GeneralLinear N ℝ) := rfl
      simp only [hG, hcoe, blockFourierCoefficient_blockRotation_mul hp]
      have hne : ((j + j' : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hjj
      have hπ : Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) *
          Complex.exp ((j' : ℂ) * (θ : ℂ) * Complex.I) = -1 := by
        rw [← Complex.exp_add, ← add_mul, ← add_mul]
        have : ((j : ℂ) + (j' : ℂ)) * (θ : ℂ) = (Real.pi : ℂ) := by
          rw [hθ]
          push_cast at hne ⊢
          have hne' : ((j : ℂ) + (j' : ℂ)) ≠ 0 := by exact_mod_cast hne
          field_simp
        rw [this, Complex.exp_pi_mul_I]
      calc Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) * blockFourierCoefficient N p j a κ *
            (Complex.exp ((j' : ℂ) * (θ : ℂ) * Complex.I) *
              blockFourierCoefficient N p j' F κ)
          = (Complex.exp ((j : ℂ) * (θ : ℂ) * Complex.I) *
              Complex.exp ((j' : ℂ) * (θ : ℂ) * Complex.I)) *
              (blockFourierCoefficient N p j a κ * blockFourierCoefficient N p j' F κ) := by
            ring
        _ = _ := by rw [hπ]; ring
    have hinv := integral_mul_left_eq_self (μ := haarK N) G r
    simp only [hrot, integral_neg] at hinv
    change ∫ κ, G κ ∂haarK N = 0
    linear_combination (-(1 : ℂ) / 2) * hinv

/-! ## The split map -/

/-- The tail condition on `a` from the position `r` on: along every induction block of `ys`
at a position `p ≥ r`, the Fourier coefficients of `a` of weight `|j| < |m|` vanish on
`O(n)`. -/
def IsTailFrom (n r : ℕ) (ys : List RealBlock) (a : Langlands.GeneralLinear n ℝ → ℂ) : Prop :=
  ∀ (p : ℕ) (d : ComplexCharacterData), r ≤ p → realInducedBlockAt ys p = some d →
    ∀ j : ℤ, |j| < |d.weight| → ∀ k ∈ unitaryCompact ℝ n, blockFourierCoefficient n p j a k = 0

theorem IsTailFrom.mono {r r' : ℕ} {ys : List RealBlock} {a : Langlands.GeneralLinear n ℝ → ℂ}
    (h : IsTailFrom n r ys a) (hr : r ≤ r') : IsTailFrom n r' ys a :=
  fun p d hp hd => h p d (hr.trans hp) hd

theorem realInducedBlockAt_append_of_le {xs ys : List RealBlock} {p : ℕ}
    (hp : realRank xs ≤ p) :
    realInducedBlockAt (xs ++ ys) p = realInducedBlockAt ys (p - realRank xs) := by
  rw [realInducedBlockAt_append]
  split_ifs with h
  · omega
  · rfl

theorem realInducedBlockAt_append_of_lt {xs ys : List RealBlock} {p : ℕ}
    (hp : p < realRank xs) :
    realInducedBlockAt (xs ++ ys) p = realInducedBlockAt xs p := by
  rw [realInducedBlockAt_append]
  simp [hp]

/-- The properties of the split map from `xs = pre ++ split ds` to `ys = pre ++ ds`. -/
def IsSplitMap (n : ℕ) (pre xs ys : List RealBlock)
    (D : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n))
    (Q : kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n)) : Prop :=
  Commutes n D ∧
  (∀ (k : Matrix.unitaryGroup (Fin n) ℝ)
      (h : kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n)),
    Q (realStandardRep n ys k h) = realStandardRep n xs k (Q h)) ∧
  (∀ h, D (Q h) = h) ∧
  (∀ (p' : ℕ), p' + 1 < realRank pre → ∀ (j : ℤ)
      (h : kFiniteFunctions (realStandardModule n ys) (unitaryCompact ℝ n)),
    (∀ k ∈ unitaryCompact ℝ n, blockFourierCoefficient n p' j h k = 0) →
      ∀ k ∈ unitaryCompact ℝ n, blockFourierCoefficient n p' j (Q h) k = 0) ∧
  ∀ a : Langlands.GeneralLinear n ℝ → ℂ, Continuous a →
    a ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) →
    IsTailFrom n (realRank pre) ys a →
    ∀ f, D f = 0 → ∫ κ : unitaryCompact ℝ n, a (κ : Langlands.GeneralLinear n ℝ) *
      (f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n = 0

theorem split_cons (b : RealBlock) (ds : List RealBlock) :
    split (b :: ds) = splitBlock b ++ split ds := rfl

theorem exists_isSplitMap : ∀ (ds pre xs ys : List RealBlock), xs = pre ++ split ds →
    ys = pre ++ ds → realRank ys = n →
    ∃ D Q, IsSplitMap n pre xs ys D Q
  | [], pre, xs, ys, hxs, hys, _ => by
    simp only [split, List.append_nil] at hxs hys
    subst hxs hys
    refine ⟨LinearMap.id, LinearMap.id, commutes_id, fun _ _ => rfl, fun _ => rfl,
      fun _ _ _ _ h0 => h0, fun a _ _ _ f hf => ?_⟩
    simp only [LinearMap.id_apply] at hf
    subst hf
    simp
  | .character c :: ds, pre, xs, ys, hxs, hys, hn => by
    obtain ⟨D, Q, hD, hQ, hDQ, hpres, hker⟩ := exists_isSplitMap ds (pre ++ [.character c])
      xs ys (by rw [hxs]; simp [split, splitBlock]) (by rw [hys]; simp) hn
    have hr : realRank pre ≤ realRank (pre ++ [RealBlock.character c]) := by
      rw [realRank_append']; omega
    exact ⟨D, Q, hD, hQ, hDQ, fun p' hp' => hpres p' (by omega),
      fun a ha haK htail => hker a ha haK (htail.mono hr)⟩
  | .induced e :: ds, pre, xs, ys, hxs, hys, hn => by
    set ℓ := e.weight.natAbs with hℓ
    set p := realRank pre with hp
    set mid := pre ++ splitBlock (.induced e) ++ ds with hmid
    have hnys : realRank (pre ++ [RealBlock.induced e] ++ ds) = n := by
      rw [← hn, hys]; simp
    have hrmid : realRank mid = n := (realRank_splitBlock_mid e).trans hnys
    have hys' : pre ++ [RealBlock.induced e] ++ ds = ys := by rw [hys]; simp
    obtain ⟨μ, hsym, hrec, hzero⟩ := exists_unsplitMultiplier ℓ
    have hF : IsBlockFrobData n mid ys p (splitParity ℓ) (splitSign ℓ) μ := by
      have h := data_unsplit (pre := pre) (post := ds) e hnys hsym hzero
      rwa [hys'] at h
    have hG : IsBlockFrobData n ys mid p (splitParity ℓ) (splitSign ℓ)⁻¹
        (fun k => (μ k)⁻¹) := by
      have h := data_resplit (pre := pre) (post := ds) e hnys hsym
      rwa [hys'] at h
    obtain ⟨D, Q, hD, hQ, hDQ, hpres, hker⟩ := exists_isSplitMap ds
      (pre ++ splitBlock (.induced e)) xs mid (by rw [hxs]; simp [split]) rfl hrmid
    have hrpre : realRank (pre ++ splitBlock (.induced e)) = p + 2 := by
      rw [realRank_append']; rfl
    -- the recurrence of `μ` for the exponents of `mid`
    have hrec' : IsRecurrent (GramFormula.realPositionExponent mid p - GramFormula.realPositionExponent mid (p + 1) + 1)
        (splitParity ℓ) μ := by
      have h0 : GramFormula.realPositionExponent mid p = GramFormula.realPositionExponent (splitBlock (.induced e)) 0 := by
        have h := realPositionExponent_mid (pre := pre) (post := ds)
          (ws := splitBlock (.induced e)) (j := 0) (by simp [splitBlock, realRank, RealBlock.rank])
        rw [Nat.add_zero] at h
        exact h
      have h1 : GramFormula.realPositionExponent mid (p + 1) =
          GramFormula.realPositionExponent (splitBlock (.induced e)) 1 :=
        realPositionExponent_mid (pre := pre) (post := ds) (ws := splitBlock (.induced e))
          (j := 1) (by simp [splitBlock, realRank, RealBlock.rank])
      rw [h0, h1]
      convert hrec using 1
      simp [GramFormula.realPositionExponent, splitBlock, lowChar, highChar, charData]
      rw [hℓ, Nat.cast_natAbs]
      ring
    have hindp : realInducedBlockAt ys p = some e := by
      rw [← hys', List.append_assoc, realInducedBlockAt_append_of_le le_rfl, Nat.sub_self]
      rfl
    refine ⟨blockFrobMap hF ∘ₗ D, Q ∘ₗ blockFrobMap hG, (commutes_blockFrobMap hF hrec').comp hD,
      fun k h => ?_, fun h => ?_, fun p' hp' j h h0 => ?_, fun a ha haK htail f hf => ?_⟩
    · simp only [LinearMap.comp_apply, blockFrobMap_rightTranslation, hQ]
    · simp only [LinearMap.comp_apply, hDQ]
      refine blockFrobMap_blockFrobMap_eq hG hF h fun j hj hne k _ => ?_
      have hμ : μ j = 0 := by
        by_contra hμ
        exact hne (mul_inv_cancel₀ hμ)
      have hjl : |j| < |e.weight| := by
        rw [Int.abs_eq_natAbs e.weight]
        exact (hzero j hj).mp hμ
      exact h.2.1.2 p e hindp j hjl k
    · simp only [LinearMap.comp_apply]
      refine hpres p' (by omega) j _ fun k hk => ?_
      exact blockFourierCoefficient_blockFrobMap_eq_zero hG (Or.inr (by omega)) h j h0 hk
    · simp only [LinearMap.comp_apply] at hf
      set g := D f with hg
      -- the modes of `g` along the block `p` lie in the window `|j| < ℓ`
      have hgm : ∀ j : ℤ, ℓ ≤ |j| → ∀ k ∈ unitaryCompact ℝ n,
          blockFourierCoefficient n p j g k = 0 := by
        intro j hj k hk
        by_cases hev : Even (j - splitParity ℓ)
        · have hμ : μ j ≠ 0 := fun h0 => absurd ((hzero j hev).mp h0) (not_lt.mpr hj)
          have h1 := blockFourierCoefficient_blockFrobMap hF g hk j
          rw [hf] at h1
          simp only [ZeroMemClass.coe_zero, blockFourierCoefficient_zero_fun] at h1
          exact (mul_eq_zero.mp h1.symm).resolve_left hμ
        · exact blockFourierCoefficient_eq_zero_of_not_even hF.lt hF.par g hev k
      have hQg : ∀ j : ℤ, ℓ ≤ |j| → ∀ k ∈ unitaryCompact ℝ n,
          blockFourierCoefficient n p j (Q g) k = 0 := fun j hj =>
        hpres p (by omega) j g (hgm j hj)
      have hsplit : (f : Langlands.GeneralLinear n ℝ → ℂ) =
          ((f - Q g : kFiniteFunctions (realStandardModule n xs) (unitaryCompact ℝ n)) :
            Langlands.GeneralLinear n ℝ → ℂ) + (Q g : Langlands.GeneralLinear n ℝ → ℂ) := by
        simp
      have h1 : D (f - Q g) = 0 := by rw [map_sub, hDQ, sub_self]
      have htail' : IsTailFrom n (realRank (pre ++ splitBlock (.induced e))) mid a := by
        intro p'' d hp'' hd
        refine htail p'' d (by omega) ?_
        rw [hrpre] at hp''
        rw [hmid, realInducedBlockAt_append_of_le (by rw [hrpre]; exact hp'')] at hd
        rw [← hys', realInducedBlockAt_append_of_le (by rw [realRank_append']; simp [RealBlock.rank]; omega)]
        rw [realRank_append'] at hd ⊢
        simpa [RealBlock.rank, realRank_splitBlock] using hd
      have hI1 := hker a ha haK htail' _ h1
      have hI2 : ∫ κ : unitaryCompact ℝ n, a (κ : Langlands.GeneralLinear n ℝ) *
          (Q g : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n = 0 := by
        refine integral_mul_eq_zero_of_modes hF.lt ha haK (continuous_coe _) (Q g).2.2
          fun j => ?_
        by_cases hj : |j| < ℓ
        · refine Or.inl (htail p e le_rfl hindp j ?_)
          rwa [Int.abs_eq_natAbs e.weight]
        · exact Or.inr (hQg (-j) (by rw [abs_neg]; exact not_lt.mp hj))
      rw [hsplit]
      simp only [Pi.add_apply, mul_add]
      rw [integral_add (integrable_mul_of_continuous ha (continuous_coe _))
        (integrable_mul_of_continuous ha (continuous_coe _)), hI1, hI2, add_zero]

/-- **The split map.** For a list `ds` of real blocks of rank `n` there are linear maps
`D` from the `O(n)`-finite functions of the standard module of `split ds` onto those of `ds`
and `Q` back with `D ∘ Q = id`, such that `D` is an intertwiner, `Q` commutes with `O(n)`,
and `∫_{O(n)} a f = 0` for every `f` in the kernel of `D` and every continuous `O(n)`-finite
`a` whose Fourier coefficients of weight `|j| < |m|` along every induction block of weight
`m` of `ds` vanish on `O(n)`. -/
theorem exists_splitMap (ds : List RealBlock) (hn : realRank ds = n) :
    ∃ (D : kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
      (Q : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n (split ds)) (unitaryCompact ℝ n)),
      IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) (split ds) D ∧
      (∀ (k : Matrix.unitaryGroup (Fin n) ℝ)
          (h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        Q (realStandardRep n ds k h) = realStandardRep n (split ds) k (Q h)) ∧
      (∀ h, D (Q h) = h) ∧
      ∀ a : Langlands.GeneralLinear n ℝ → ℂ, Continuous a →
        a ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
          (unitaryCompact ℝ n) →
        (∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
          ∀ j : ℤ, |j| < |d.weight| → ∀ k ∈ unitaryCompact ℝ n,
            blockFourierCoefficient n p j a k = 0) →
        ∀ f, D f = 0 → ∫ κ : unitaryCompact ℝ n, a (κ : Langlands.GeneralLinear n ℝ) *
          (f : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n = 0 := by
  obtain ⟨D, Q, hD, hQ, hDQ, -, hker⟩ :=
    exists_isSplitMap ds [] (split ds) ds (by simp) (by simp) hn
  exact ⟨D, Q, hD.isRealStandardIntertwiner, hQ, hDQ,
    fun a ha haK htail => hker a ha haK fun p d _ hd => htail p d hd⟩

end RealSplitFrobenius

end Langlands.Archimedean
