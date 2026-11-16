import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealRankOneStepFiltration
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible

/-!
# Frobenius maps between real standard modules along a block

Let `ds` and `es` be lists of real blocks that agree outside the positions `p, p + 1`, where
the exponents of the position characters are exchanged. For a multiplier `μ : ℤ → ℂ` on the
parity class `ε` of the block, symmetric with sign `σ`, the block Jacquet functional
`ℓ_μ = blockJacquet n ds p μ` on the `O(n)`-finite functions of the standard module of `ds`
has the signs of `es` and the `ρ`-shifted exponents of `es`. Its Frobenius functions
`frobFun (realStandardRep n ds) ℓ_μ (shiftedExponent n es) (positionSign n es)` lie in the
standard module of `es` (`IsBlockFrobData.frobFun_mem`); this gives the linear map
`blockFrobMap h` from the `O(n)`-finite functions of the standard module of `ds` to those of
the standard module of `es`.

* `blockFourierCoefficient_blockFrobMap`: on `O(n)`, `Φ_j (blockFrobMap h f) = μ_j Φ_j f`.
* `blockFrobMap_rightTranslation`: the map commutes with right translation by `O(n)`, for
  every `μ`.
* `blockFrobMap_rightDerivative`, `isRealIntertwinerModulo_blockFrobMap`: if `μ` satisfies the
  recurrence of `IsRecurrent` for `δ = t_p - t_{p+1} + 1` (`t` the exponents of `ds`), the map
  also commutes with the right derivatives, so it is an intertwiner.
* `eq_of_blockFourierCoefficient_eq`: two `O(n)`-finite functions of a standard module with
  the same block Fourier coefficients on `O(n)` are equal.
* `blockFrobMap_blockFrobMap_eq`: a composite of two such maps whose multipliers multiply to
  `1` on the modes of `f` is the identity on `f`.
* `IsBlockFrobData.of_mid`: the data for `ds = pre ++ ws ++ post`, `es = pre ++ ws' ++ post`
  with `ws` and `ws'` of rank two.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealBlockFrobeniusMap

open RealJacquetFrobenius RealBlockRotation RealBlockFourierFinite RealBlockMultiplier
open RealBlockJacquet RealBlockPosition
open Langlands.LocalFactor.Archimedean

/-- Data for the Frobenius map along the block `p, p + 1` from the standard module of `ds` to
that of `es` with multiplier `μ`: the block lies inside the rank `n` of `es`; the signs and
exponents of `es` agree with those of `ds` off the block; the exponents are exchanged on the
block; the modes of `ds` on the block live on the parity class `ε`; `μ` is symmetric with
sign `σ` on it and the signs of `es` on the block are those of `ds` times `σ`; every
induction block of `es` off `p` is an induction block of `ds` disjoint from the block; and
`μ` vanishes on the window of an induction block of `es` at `p`. -/
structure IsBlockFrobData (n : ℕ) (ds es : List RealBlock) (p : ℕ) (ε : ℤ) (σ : ℂ)
    (μ : ℤ → ℂ) : Prop where
  lt : p + 1 < n
  rank : realRank es = n
  sign_off : ∀ i : ℕ, i ≠ p → i ≠ p + 1 → realPositionSign es i = realPositionSign ds i
  exp_off : ∀ i : ℕ, i ≠ p → i ≠ p + 1 → GramFormula.realPositionExponent es i = GramFormula.realPositionExponent ds i
  exp_p : GramFormula.realPositionExponent es p = GramFormula.realPositionExponent ds (p + 1)
  exp_q : GramFormula.realPositionExponent es (p + 1) = GramFormula.realPositionExponent ds p
  par : (-1 : ℂ) ^ ε = realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1)
  sym : IsSymmetric ε σ μ
  sign_p : (-1 : ℂ) ^ (realPositionSign es p).val = realPositionCharacter ds p (-1) * σ
  sign_q : (-1 : ℂ) ^ (realPositionSign es (p + 1)).val =
    realPositionCharacter ds (p + 1) (-1) * σ
  induced_off : ∀ (i : ℕ) (d : ComplexCharacterData), i ≠ p → realInducedBlockAt es i = some d →
    (p + 1 < i ∨ i + 1 < p) ∧ realInducedBlockAt ds i = some d
  induced_p : ∀ d : ComplexCharacterData, realInducedBlockAt es p = some d →
    ∀ j : ℤ, Even (j - ε) → |j| < |d.weight| → μ j = 0

variable {n : ℕ} {ds es : List RealBlock} {p : ℕ} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}

namespace IsBlockFrobData

variable (h : IsBlockFrobData n ds es p ε σ μ)
include h

theorem neg_one_pow_positionSign_off (i : Fin n) (hi1 : i ≠ ia h.lt) (hi2 : i ≠ ib h.lt) :
    (-1 : ℂ) ^ (positionSign n es i).val = realPositionCharacter ds i (-1) := by
  rw [realPositionCharacter_neg_one, positionSign,
    h.sign_off i (fun e => hi1 (Fin.ext e)) (fun e => hi2 (Fin.ext e))]

/-- The sign matrices act on `ℓ_μ` by the signs of `es`. -/
theorem hsign (j : Fin n) (v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockJacquet n ds p μ (realStandardRep n ds (signReflection n j) v) =
      (-1) ^ (positionSign n es j).val * blockJacquet n ds p μ v :=
  blockJacquet_hsign h.lt h.par h.sym (e := positionSign n es)
    (fun i hi1 hi2 => h.neg_one_pow_positionSign_off i hi1 hi2) h.sign_p h.sign_q j v

/-- The modes of `es` on the block also live on the parity class `ε`, when `σ² = 1`. -/
theorem par_target (hσ : σ ^ 2 = 1) :
    (-1 : ℂ) ^ ε = realPositionCharacter es p (-1) * realPositionCharacter es (p + 1) (-1) := by
  rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one, h.sign_p, h.sign_q, h.par]
  linear_combination
    (-(realPositionCharacter ds p (-1) * realPositionCharacter ds (p + 1) (-1))) * hσ

/-- The Frobenius functions of `ℓ_μ` are `O(n)`-finite functions of the standard module
of `es`. -/
theorem frobFun_mem (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    frobFun (realStandardRep n ds) (blockJacquet n ds p μ) (shiftedExponent n es)
        (positionSign n es) f ∈ kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) := by
  have hgk := isRealGKModule_realStandardModule n ds
  have hps : frobFun (realStandardRep n ds) (blockJacquet n ds p μ) (shiftedExponent n es)
      (positionSign n es) f ∈ principalSeries ℝ n (realPositionCharacter es) := by
    rw [← principalSeries_posChar_shiftedExponent]
    exact ⟨contMDiff_frobFun h.hsign hgk.1 hgk.2.1 f, fun a u g => frobFun_left h.hsign f a u g⟩
  refine ⟨mem_realStandardModule_of_unitaryCompact h.rank hps fun i d hd j hj k hk => ?_,
    frobFun_mem_kFiniteVectors h.hsign f (hgk.1 f)⟩
  by_cases hi : i = p
  · subst hi
    rw [blockFourierCoefficient_frobFun h.lt h.hsign f hk j]
    by_cases hj' : Even (j - ε)
    · rw [h.induced_p d hd j hj' hj, zero_mul]
    · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj' k, mul_zero]
  · obtain ⟨hdis, hd'⟩ := h.induced_off i d hi hd
    exact blockFourierCoefficient_frobFun_eq_zero hdis h.hsign f j
      (fun g => f.2.1.2 i d hd' j hj g) hk

/-- With the recurrence for `δ = t_p - t_{p+1} + 1`, `ℓ_μ` is a real Jacquet functional with
the `ρ`-shifted exponents and the signs of `es`. -/
theorem isRealJacquetFunctional
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds p - GramFormula.realPositionExponent ds (p + 1) + 1) ε μ) :
    IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds)
      (blockJacquet n ds p μ) (shiftedExponent n es) (positionSign n es) := by
  refine isRealJacquetFunctional_blockJacquet h.lt (τ := fun i => GramFormula.realPositionExponent ds i)
    (fun i x => realPositionCharacter_exp ds i x) h.par ?_ h.sym ?_ ?_ ?_
    (fun i hi1 hi2 => h.neg_one_pow_positionSign_off i hi1 hi2) h.sign_p h.sign_q
  · convert hrec using 1
    simp only [ia, ib]
    push_cast
    ring
  · intro i hi1 hi2
    rw [shiftedExponent, h.exp_off i (fun e => hi1 (Fin.ext e)) (fun e => hi2 (Fin.ext e))]
  · simp only [shiftedExponent, ia, ib, h.exp_p]
    push_cast
    ring
  · simp only [shiftedExponent, ia, ib, h.exp_q]
    push_cast
    ring

end IsBlockFrobData

/-- The Frobenius map along the block: `f ↦ frobFun (realStandardRep n ds) ℓ_μ a e f` with
the `ρ`-shifted exponents `a` and the signs `e` of `es`, from the `O(n)`-finite functions of
the standard module of `ds` to those of the standard module of `es`. -/
def blockFrobMap (h : IsBlockFrobData n ds es p ε σ μ) :
    kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) :=
  LinearMap.codRestrict _ (frobLin (realStandardRep n ds) (blockJacquet n ds p μ)
    (shiftedExponent n es) (positionSign n es)) h.frobFun_mem

section Map

variable (h : IsBlockFrobData n ds es p ε σ μ)

theorem blockFrobMap_apply_coe
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    ((blockFrobMap h f : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ) =
      frobFun (realStandardRep n ds) (blockJacquet n ds p μ) (shiftedExponent n es)
        (positionSign n es) f :=
  rfl

/-- On `O(n)`, `blockFrobMap h f (g) = (2π)⁻¹ Σᶠ_i μ_i Φ_i f (g)`. -/
theorem blockFrobMap_apply_of_mem
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {g : Langlands.GeneralLinear n ℝ} (hg : g ∈ unitaryCompact ℝ n) :
    ((blockFrobMap h f : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ) g =
      (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ i : ℤ, μ i * blockFourierCoefficient n p i f g :=
  frobFun_apply_of_mem h.hsign f hg

/-- **Multiplier on `O(n)`.** `Φ_j (blockFrobMap h f) (k) = μ_j Φ_j f (k)` for `k ∈ O(n)`. -/
theorem blockFourierCoefficient_blockFrobMap
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) (j : ℤ) :
    blockFourierCoefficient n p j
        ((blockFrobMap h f : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
          Langlands.GeneralLinear n ℝ → ℂ) k =
      μ j * blockFourierCoefficient n p j f k :=
  blockFourierCoefficient_frobFun h.lt h.hsign f hk j

/-- The map commutes with right translation by `O(n)`. -/
theorem blockFrobMap_rightTranslation (k : Matrix.unitaryGroup (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockFrobMap h (realStandardRep n ds k f) = realStandardRep n es k (blockFrobMap h f) := by
  apply Subtype.ext
  rw [blockFrobMap_apply_coe, realStandardRep_apply_coe, blockFrobMap_apply_coe]
  exact frobFun_rightTranslation h.hsign ⟨Unitary.toUnits k, k.2⟩ f

/-- With the recurrence, the map commutes with the right derivatives. -/
theorem blockFrobMap_rightDerivative
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds p - GramFormula.realPositionExponent ds (p + 1) + 1) ε μ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    blockFrobMap h (realStandardLie n ds (1 ⊗ₜ X) f) =
      realStandardLie n es (1 ⊗ₜ X) (blockFrobMap h f) := by
  apply Subtype.ext
  rw [blockFrobMap_apply_coe, realStandardLie_one_tmul_apply_coe, blockFrobMap_apply_coe]
  funext g
  exact frobFun_rightDerivative (isRealGKModule_realStandardModule n ds)
    (h.isRealJacquetFunctional hrec) X f g

/-- Right translation of an `O(n)`-finite function of the standard module as the action of
`realStandardRep`. -/
theorem mk_rightTranslation_eq (ds : List RealBlock) (k : unitaryCompact ℝ n)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    (⟨_, hf⟩ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) =
      realStandardRep n ds ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩
        f := by
  apply Subtype.ext
  rw [realStandardRep_apply_coe]
  have hk : (Unitary.toUnits
      (⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) : Langlands.GeneralLinear n ℝ) =
      (k : Langlands.GeneralLinear n ℝ) :=
    Units.ext rfl
  rw [hk]

/-- The right derivative of an `O(n)`-finite function of the standard module as the action
of `realStandardLie`. -/
theorem mk_rightDerivative_eq (ds : List RealBlock) (X : Matrix (Fin n) (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    (⟨_, hf⟩ : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) =
      realStandardLie n ds (1 ⊗ₜ X) f := by
  apply Subtype.ext
  rw [realStandardLie_one_tmul_apply_coe]

/-- The map commutes with right translation by `O(n)`, in the form of the first clause of
`IsRealIntertwinerModulo`. -/
theorem blockFrobMap_mk_rightTranslation (k : unitaryCompact ℝ n)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (blockFrobMap h f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
    blockFrobMap h ⟨_, hf⟩ = ⟨_, hg⟩ := by
  rw [mk_rightTranslation_eq ds k f hf, mk_rightTranslation_eq es k _ hg,
    blockFrobMap_rightTranslation]

/-- With the recurrence, the map commutes with the right derivatives, in the form of the
second clause of `IsRealIntertwinerModulo`. -/
theorem blockFrobMap_mk_rightDerivative
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds p - GramFormula.realPositionExponent ds (p + 1) + 1) ε μ)
    (X : Matrix (Fin n) (Fin n) ℝ)
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hg : rightDerivative (matrixModel ℝ n) X (blockFrobMap h f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
    blockFrobMap h ⟨_, hf⟩ = ⟨_, hg⟩ := by
  rw [mk_rightDerivative_eq ds X f hf, mk_rightDerivative_eq es X _ hg,
    blockFrobMap_rightDerivative h hrec]

/-- **Intertwiner.** With the recurrence for `δ = t_p - t_{p+1} + 1`, the map is an
intertwiner modulo every subspace `M`. -/
theorem isRealIntertwinerModulo_blockFrobMap
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds p - GramFormula.realPositionExponent ds (p + 1) + 1) ε μ)
    (M : Submodule ℂ (kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n))) :
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
  · rw [blockFrobMap_mk_rightDerivative h hrec X f _
      (rightDerivative_mem_kFiniteFunctions_realStandardModule n es (blockFrobMap h f).2 X),
      sub_self]
    exact M.zero_mem

end Map

/-! ## Uniqueness and composites -/

/-- Two `O(n)`-finite functions of a standard module with the same block Fourier
coefficients on `O(n)` are equal. -/
theorem eq_of_blockFourierCoefficient_eq (hp : p + 1 < n)
    {f g : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)}
    (hfg : ∀ (j : ℤ) (k : Langlands.GeneralLinear n ℝ), k ∈ unitaryCompact ℝ n →
      blockFourierCoefficient n p j f k = blockFourierCoefficient n p j g k) : f = g := by
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2.1.1 g.2.1.1 fun k hk => ?_
  rw [eq_finsum_blockFourierCoefficient hp (continuous_coe f) f.2.2 hk,
    eq_finsum_blockFourierCoefficient hp (continuous_coe g) g.2.2 hk]
  congr 2
  funext j
  exact hfg j k hk

/-- A composite of two Frobenius maps along the same block is the identity on `f` when the
multipliers multiply to `1` on the modes of the parity class that do not vanish on `O(n)`
for `f`. -/
theorem blockFrobMap_blockFrobMap_eq (h : IsBlockFrobData n ds es p ε σ μ) {σ' : ℂ}
    {μ' : ℤ → ℂ} (h' : IsBlockFrobData n es ds p ε σ' μ')
    (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hf : ∀ j : ℤ, Even (j - ε) → μ' j * μ j ≠ 1 →
      ∀ k ∈ unitaryCompact ℝ n, blockFourierCoefficient n p j f k = 0) :
    blockFrobMap h' (blockFrobMap h f) = f := by
  refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
  rw [blockFourierCoefficient_blockFrobMap h' _ hk, blockFourierCoefficient_blockFrobMap h _ hk,
    ← mul_assoc]
  by_cases hj : Even (j - ε)
  · by_cases h1 : μ' j * μ j = 1
    · rw [h1, one_mul]
    · rw [hf j hj h1 k hk, mul_zero]
  · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj k, mul_zero]

/-! ## Lists `pre ++ ws ++ post` -/

/-- The data for `ds = pre ++ ws ++ post` and `es = pre ++ ws' ++ post` along the block at
`p = realRank pre`, when `ws` and `ws'` have rank two: the conditions only concern the
positions `0, 1` of `ws` and `ws'`. -/
theorem IsBlockFrobData.of_mid {pre ws ws' post : List RealBlock}
    (hn : realRank (pre ++ ws' ++ post) = n) (hws : realRank ws = 2) (hws' : realRank ws' = 2)
    (hexp0 : GramFormula.realPositionExponent ws' 0 = GramFormula.realPositionExponent ws 1)
    (hexp1 : GramFormula.realPositionExponent ws' 1 = GramFormula.realPositionExponent ws 0)
    (hpar : (-1 : ℂ) ^ ε = realPositionCharacter ws 0 (-1) * realPositionCharacter ws 1 (-1))
    (hsym : IsSymmetric ε σ μ)
    (hsign0 : (-1 : ℂ) ^ (realPositionSign ws' 0).val = realPositionCharacter ws 0 (-1) * σ)
    (hsign1 : (-1 : ℂ) ^ (realPositionSign ws' 1).val = realPositionCharacter ws 1 (-1) * σ)
    (hind : ∀ d : ComplexCharacterData, realInducedBlockAt ws' 0 = some d →
      ∀ j : ℤ, Even (j - ε) → |j| < |d.weight| → μ j = 0) :
    IsBlockFrobData n (pre ++ ws ++ post) (pre ++ ws' ++ post) (realRank pre) ε σ μ := by
  have hr : realRank pre + 2 + realRank post = n := by
    rw [← hn, ← hws']
    simp [realRank, List.map_append, List.sum_append, add_assoc]
  have h0 : 0 < realRank ws := by omega
  have h1 : 1 < realRank ws := by omega
  have h0' : 0 < realRank ws' := by omega
  have h1' : 1 < realRank ws' := by omega
  have hrr : realRank ws' = realRank ws := by omega
  have hoff : ∀ i : ℕ, i ≠ realRank pre → i ≠ realRank pre + 1 →
      i < realRank pre ∨ realRank pre + realRank ws' ≤ i := fun i hi1 hi2 => by omega
  refine
    { lt := by omega
      rank := hn
      sign_off := fun i hi1 hi2 => realPositionSign_of_not_mid hrr (hoff i hi1 hi2)
      exp_off := fun i hi1 hi2 => realPositionExponent_of_not_mid hrr (hoff i hi1 hi2)
      exp_p := ?_
      exp_q := ?_
      par := ?_
      sym := hsym
      sign_p := ?_
      sign_q := ?_
      induced_off := ?_
      induced_p := ?_ }
  · have e1 := realPositionExponent_mid pre ws' post h0'
    have e2 := realPositionExponent_mid pre ws post h1
    rw [add_zero] at e1
    rw [e1, e2, hexp0]
  · rw [realPositionExponent_mid pre ws' post h1', ← add_zero (realRank pre),
      realPositionExponent_mid pre ws post h0, hexp1]
  · rw [← add_zero (realRank pre), realPositionCharacter_mid pre ws post h0, add_zero,
      realPositionCharacter_mid pre ws post h1, hpar]
  · rw [← add_zero (realRank pre), realPositionSign_mid pre ws' post h0',
      realPositionCharacter_mid pre ws post h0, hsign0]
  · rw [realPositionSign_mid pre ws' post h1', realPositionCharacter_mid pre ws post h1, hsign1]
  · intro i d hi hd
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · refine ⟨Or.inr (lt_of_realInducedBlockAt_of_lt hd hlt), ?_⟩
      rw [← realInducedBlockAt_of_not_mid hrr (Or.inl hlt)]
      exact hd
    · by_cases hq : i = realRank pre + 1
      · subst hq
        rw [realInducedBlockAt_mid pre ws' post h1',
          realInducedBlockAt_one_of_realRank_eq_two hws'] at hd
        exact absurd hd (by simp)
      · refine ⟨Or.inl (by omega), ?_⟩
        rw [← realInducedBlockAt_of_not_mid hrr (Or.inr (by omega))]
        exact hd
  · intro d hd
    rw [← add_zero (realRank pre), realInducedBlockAt_mid pre ws' post h0'] at hd
    exact hind d hd

end RealBlockFrobeniusMap

end Langlands.Archimedean
